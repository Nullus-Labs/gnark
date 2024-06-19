package groth16

import (
	"encoding/binary"
	"errors"
	"math/big"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/mimc"
	cs "github.com/consensys/gnark/constraint/bn254"
	"github.com/consensys/gnark/frontend"
)

func IVCSetup(r1cs *cs.R1CS) (pk_e, pk_w PedersenKey, err error) {
	if pk_e, err = PedersenSetup(r1cs.GetNbConstraints()); err != nil {
		return
	}
	if pk_w, err = PedersenSetup(r1cs.GetNbConstraints()); err != nil {
		return
	}
	return
}

func IVCProve(r1cs *cs.R1CS, pk_e, pk_w PedersenKey, inputs []byte) (*CommitedRelaxedR1CS, bn254.G1Affine, error) {
	// Separate inputs into 64 byte blocks and hash them
	// Do the SHA256 message pending
	var num_iter int
	inputLen := len(inputs)
	if inputLen%64 < 56 {
		num_iter = inputLen/64 + 1
		var tmp [64]byte
		// Copy the last remaining block to tmp
		copy(tmp[:], inputs[inputLen/64*64:])
		// Append 0x80 to the end of the block
		tmp[inputLen%64] = 0x80
		// Put inputLen * 8 in big endian
		inputBitLen := inputLen << 3
		for i := 0; i < 8; i++ {
			tmp[63-i] = byte(inputBitLen >> (i << 3))
		}
		inputs = append(inputs, tmp[:]...)
	} else {
		num_iter = inputLen/64 + 2
		var tmp [64]byte
		// Copy the last remaining block to tmp
		copy(tmp[:], inputs[inputLen/64*64:])
		// Append 0x80 to the end of the block
		tmp[inputLen%64] = 0x80
		inputs = append(inputs, tmp[:]...)
		// Clear tmp
		for i := range tmp {
			tmp[i] = 0
		}
		// Put inputLen * 8 in big endian at the end of tmp
		inputBitLen := inputLen << 3
		for i := 0; i < 8; i++ {
			tmp[63-i] = byte(inputBitLen >> (i << 3))
		}
		inputs = append(inputs, tmp[:]...)
	}
	initialState := [8]uint32{
		0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
		0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
	}
	var state []uint32
	internal, secret, public := r1cs.GetNbVariables()
	bigInstance, err := NewCommittedRelaxedR1CS(len(r1cs.Coefficients), internal+secret+public, public, pk_e, pk_w)
	if err != nil {
		return nil, bn254.G1Affine{}, err
	}
	comT := bigInstance.Com_E
	// Make assignment
	assignment, state, err := makeAssignment(bigInstance, bigInstance, comT, 0, initialState[:], initialState[:], inputs[:64])
	if err != nil {
		return nil, bn254.G1Affine{}, err
	}
	// Generate Witness
	witness, err := frontend.NewWitness(assignment, bn254.ID.ScalarField())
	if err != nil {
		return nil, bn254.G1Affine{}, err
	}
	witnessVec, ok := witness.Vector().(fr.Vector)
	if !ok {
		return nil, bn254.G1Affine{}, errors.New("invalid witness")
	}
	smallInstance, err := NewCommittedRelaxedR1CSFromInstance(r1cs, witnessVec, pk_e, pk_w)
	if err != nil {
		return nil, bn254.G1Affine{}, err
	}
	for i := 1; i < num_iter; i++ {
		if bigInstance, comT, err = bigInstance.FoldProve(r1cs, smallInstance, pk_e); err != nil {
			return nil, bn254.G1Affine{}, err
		}
		// TODO: Compute the new witness of F' and generate the new smallInstance
		// Make assignment
		assignment, state, err = makeAssignment(bigInstance, smallInstance, comT, i, initialState[:], state, inputs[i*64:(i+1)*64])
		if err != nil {
			return nil, bn254.G1Affine{}, err
		}
		// Generate Witness
		witness, err = frontend.NewWitness(assignment, bn254.ID.ScalarField())
		if err != nil {
			return nil, bn254.G1Affine{}, err
		}
		witnessVec, ok = witness.Vector().(fr.Vector)
		if !ok {
			return nil, bn254.G1Affine{}, errors.New("invalid witness")
		}
		smallInstance, err = NewCommittedRelaxedR1CSFromInstance(r1cs, witnessVec, pk_e, pk_w)
		if err != nil {
			return nil, bn254.G1Affine{}, err
		}
	}
	bigInstance, comT, err = bigInstance.FoldProve(r1cs, smallInstance, pk_e)
	if err != nil {
		return nil, bn254.G1Affine{}, err
	}
	return bigInstance, comT, nil
}

func makeAssignment(bigInstance, smallInstance *CommitedRelaxedR1CS, comT bn254.G1Affine, idx int, z0, zi []uint32, wi []byte) (*ExpandCircuit, []uint32, error) {
	circuit := new(ExpandCircuit)
	circuit.Idx = idx
	circuit.Z0 = make([]frontend.Variable, len(z0))
	circuit.Zi = make([]frontend.Variable, len(zi))
	circuit.Wi = make([]frontend.Variable, len(wi))
	for i := 0; i < len(z0); i++ {
		circuit.Z0[i] = z0[i]
	}
	for i := 0; i < len(zi); i++ {
		circuit.Zi[i] = zi[i]
	}
	for i := 0; i < len(wi); i++ {
		circuit.Wi[i] = wi[i]
	}
	circuit.BigInstance.Com_E = makeG1Point(bigInstance.Com_E)
	circuit.BigInstance.U = bigInstance.U
	circuit.BigInstance.Com_W = makeG1Point(bigInstance.Com_W)
	if len(bigInstance.X) != 3 {
		return nil, nil, errors.New("invalid bigInstance")
	}
	circuit.BigInstance.X[0] = bigInstance.X[0]
	circuit.BigInstance.X[1] = bigInstance.X[1]
	circuit.BigInstance.X[2] = bigInstance.X[2]
	circuit.SmallInstance.Com_E = makeG1Point(smallInstance.Com_E)
	circuit.SmallInstance.U = smallInstance.U
	circuit.SmallInstance.Com_W = makeG1Point(smallInstance.Com_W)
	if len(smallInstance.X) != 3 {
		return nil, nil, errors.New("invalid smallInstance")
	}
	circuit.SmallInstance.X[0] = smallInstance.X[0]
	circuit.SmallInstance.X[1] = smallInstance.X[1]
	circuit.SmallInstance.X[2] = smallInstance.X[2]
	circuit.Com_T = makeG1Point(comT)
	// TODO: Compute the hash outside of the circuit
	var hashInputs [][]byte
	hashInputs = append(hashInputs, intToByteArray(idx+1))
	for _, z := range z0 {
		hashInputs = append(hashInputs, u32ToByteArray(z))
	}
	new_z := sha256Block(zi, wi)
	for _, z := range new_z {
		hashInputs = append(hashInputs, u32ToByteArray(z))
	}
	hashInputs = appendG1Point(hashInputs, bigInstance.Com_E)
	hashInputs = append(hashInputs, bigInstance.U.Marshal())
	hashInputs = appendG1Point(hashInputs, bigInstance.Com_W)
	hashInputs = append(hashInputs, bigInstance.X[0].Marshal())

	out := getMiMCHash(hashInputs...)
	// convert out to fr element
	outFr := fr.Element{}
	outFr.SetBytes(out)
	circuit.U = 1
	circuit.X_Out = outFr
	return circuit, new_z, nil
}

func makeG1Point(p bn254.G1Affine) G1Point {
	pJac := bn254.G1Jac{}
	pJac.FromAffine(&p)
	return G1Point{X: pJac.X.BigInt(new(big.Int)), Y: pJac.Y.BigInt(new(big.Int)), Z: pJac.Z.BigInt(new(big.Int))}
}

func getMiMCHash(inputs ...[]byte) []byte {
	var inputBuf [32]byte
	hasher := mimc.NewMiMC()
	for _, input := range inputs {
		if len(input) > 32 {
			panic("input too long")
		}
		// Copy input to the last of inputBuf
		copy(inputBuf[32-len(input):], input)
		hasher.Write(inputBuf[:])
		// clear input buf
		for i := range inputBuf {
			inputBuf[i] = 0
		}
	}
	return hasher.Sum([]byte{})
}

// SHA-256 constants
var k = [64]uint32{
	0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
	0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
	0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
	0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
	0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
	0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
	0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
	0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
	0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
	0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
	0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
	0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
	0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
	0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
	0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
	0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
}

func rightRotate(x uint32, n uint32) uint32 {
	return (x >> n) | (x << (32 - n))
}

func sha256Block(state []uint32, block []byte) []uint32 {
	// Extend the first 16 words into the remaining 48 words w[16..63] of the message schedule array
	var w [64]uint32
	for i := 0; i < 16; i++ {
		w[i] = binary.BigEndian.Uint32(block[i*4 : (i+1)*4])
	}

	for i := 16; i < 64; i++ {
		s0 := rightRotate(w[i-15], 7) ^ rightRotate(w[i-15], 18) ^ (w[i-15] >> 3)
		s1 := rightRotate(w[i-2], 17) ^ rightRotate(w[i-2], 19) ^ (w[i-2] >> 10)
		w[i] = w[i-16] + s0 + w[i-7] + s1
	}

	// Initialize working variables to current hash value
	a, b, c, d, e, f, g, h := state[0], state[1], state[2], state[3], state[4], state[5], state[6], state[7]

	// Compression function main loop
	for i := 0; i < 64; i++ {
		S1 := rightRotate(e, 6) ^ rightRotate(e, 11) ^ rightRotate(e, 25)
		ch := (e & f) ^ ((^e) & g)
		temp1 := h + S1 + ch + k[i] + w[i]
		S0 := rightRotate(a, 2) ^ rightRotate(a, 13) ^ rightRotate(a, 22)
		maj := (a & b) ^ (a & c) ^ (b & c)
		temp2 := S0 + maj

		h = g
		g = f
		f = e
		e = d + temp1
		d = c
		c = b
		b = a
		a = temp1 + temp2
	}

	// Add the compressed chunk to the current hash value
	state[0] += a
	state[1] += b
	state[2] += c
	state[3] += d
	state[4] += e
	state[5] += f
	state[6] += g
	state[7] += h
	return state
}

func u32ToByteArray(in uint32) []byte {
	out := make([]byte, 4)
	binary.BigEndian.PutUint32(out, in)
	return out
}

func intToByteArray(in int) []byte {
	// Put the number in the end
	out := make([]byte, 8)
	for i := 0; i < 8; i++ {
		out[7-i] = byte(in >> (i << 3))
	}
	return out
}

func appendG1Point(out [][]byte, in bn254.G1Affine) [][]byte {
	inJac := bn254.G1Jac{}
	inJac.FromAffine(&in)
	out = append(out, inJac.X.Marshal())
	out = append(out, inJac.Y.Marshal())
	out = append(out, inJac.Z.Marshal())
	return out
}
