package groth16

import (
	"github.com/consensys/gnark/frontend"
)

const chunk = 64

var _K = []uint32{
	0x428a2f98,
	0x71374491,
	0xb5c0fbcf,
	0xe9b5dba5,
	0x3956c25b,
	0x59f111f1,
	0x923f82a4,
	0xab1c5ed5,
	0xd807aa98,
	0x12835b01,
	0x243185be,
	0x550c7dc3,
	0x72be5d74,
	0x80deb1fe,
	0x9bdc06a7,
	0xc19bf174,
	0xe49b69c1,
	0xefbe4786,
	0x0fc19dc6,
	0x240ca1cc,
	0x2de92c6f,
	0x4a7484aa,
	0x5cb0a9dc,
	0x76f988da,
	0x983e5152,
	0xa831c66d,
	0xb00327c8,
	0xbf597fc7,
	0xc6e00bf3,
	0xd5a79147,
	0x06ca6351,
	0x14292967,
	0x27b70a85,
	0x2e1b2138,
	0x4d2c6dfc,
	0x53380d13,
	0x650a7354,
	0x766a0abb,
	0x81c2c92e,
	0x92722c85,
	0xa2bfe8a1,
	0xa81a664b,
	0xc24b8b70,
	0xc76c51a3,
	0xd192e819,
	0xd6990624,
	0xf40e3585,
	0x106aa070,
	0x19a4c116,
	0x1e376c08,
	0x2748774c,
	0x34b0bcb5,
	0x391c0cb3,
	0x4ed8aa4a,
	0x5b9cca4f,
	0x682e6ff3,
	0x748f82ee,
	0x78a5636f,
	0x84c87814,
	0x8cc70208,
	0x90befffa,
	0xa4506ceb,
	0xbef9a3f7,
	0xc67178f2,
}

var KBits [][]frontend.Variable

func init() {
	KBits = make([][]frontend.Variable, len(_K))
	for i := 0; i < len(KBits); i++ {
		KBits[i] = toBinary32(_K[i])
	}
}

func toBinary32(x uint32) []frontend.Variable {
	bits := make([]frontend.Variable, 32)
	for i := 0; i < 32; i++ {
		bits[i] = x & 1
		x >>= 1
	}
	return bits
}

func block(api frontend.API, hh []frontend.Variable, p []frontend.Variable) []frontend.Variable {
	for len(p) >= chunk {
		msg_schedule := [][]frontend.Variable{}
		for t := 0; t < 64; t++ {
			if t <= 15 {
				msg_schedule = append(msg_schedule, BytesToBits(api, p[t*4:t*4+4]))
			} else {
				term1 := api.FromBinary(Sigma1(api, msg_schedule[t-2])...)
				term2 := api.FromBinary(msg_schedule[t-7]...)
				term3 := api.FromBinary(Sigma0(api, msg_schedule[t-15])...)
				term4 := api.FromBinary(msg_schedule[t-16]...)
				schedule := api.Add(api.Add(api.Add(term1, term2), term3), term4)
				schedule_bits := api.ToBinary(schedule, 34)[:32] // will throw error if directly do ToBinary(xxx, 32). Not know why...
				msg_schedule = append(msg_schedule, schedule_bits)
			}
		}

		a, b, c, d, e, f, g, h := hh[0], hh[1], hh[2], hh[3], hh[4], hh[5], hh[6], hh[7]
		a_bit, b_bit, c_bit, e_bit, f_bit, g_bit := api.ToBinary(a, 32), api.ToBinary(b, 32), api.ToBinary(c, 32), api.ToBinary(e, 32), api.ToBinary(f, 32), api.ToBinary(g, 32)

		for t := 0; t < 64; t++ {
			t1_term1 := h
			t1_term2 := api.FromBinary(CapSigma1(api, e_bit)...)
			t1_term3 := api.FromBinary(Ch(api, e_bit, f_bit, g_bit)...)
			t1_term4 := _K[t]
			t1_term5 := api.FromBinary(msg_schedule[t]...)
			t1 := api.Add(api.Add(api.Add(api.Add(t1_term1, t1_term2), t1_term3), t1_term4), t1_term5)
			t2 := api.Add(api.FromBinary(CapSigma0(api, a_bit)...), api.FromBinary(Maj(api, a_bit, b_bit, c_bit)...))
			new_a_bit := api.ToBinary(api.Add(t1, t2), 35)[:32]
			new_e_bit := api.ToBinary(api.Add(d, t1), 35)[:32]
			a, b, c, d, e, f, g, h = api.FromBinary(new_a_bit...), a, b, c, api.FromBinary(new_e_bit...), e, f, g
			a_bit, b_bit, c_bit, e_bit, f_bit, g_bit = new_a_bit, a_bit, b_bit, new_e_bit, e_bit, f_bit
		}

		hh[0] = api.FromBinary(api.ToBinary(api.Add(hh[0], a), 33)[:32]...)
		hh[1] = api.FromBinary(api.ToBinary(api.Add(hh[1], b), 33)[:32]...)
		hh[2] = api.FromBinary(api.ToBinary(api.Add(hh[2], c), 33)[:32]...)
		hh[3] = api.FromBinary(api.ToBinary(api.Add(hh[3], d), 33)[:32]...)
		hh[4] = api.FromBinary(api.ToBinary(api.Add(hh[4], e), 33)[:32]...)
		hh[5] = api.FromBinary(api.ToBinary(api.Add(hh[5], f), 33)[:32]...)
		hh[6] = api.FromBinary(api.ToBinary(api.Add(hh[6], g), 33)[:32]...)
		hh[7] = api.FromBinary(api.ToBinary(api.Add(hh[7], h), 33)[:32]...)
		p = p[chunk:]
	}
	return hh
}

func BytesToVal(api frontend.API, vals []frontend.Variable) frontend.Variable {
	// Big-end
	ret := vals[0]
	for i := 1; i < len(vals); i++ {
		ret = api.Add(api.Mul(ret, 256), vals[i])
	}
	return ret
}

func BytesToBits(api frontend.API, vals []frontend.Variable) []frontend.Variable {
	// Big-end
	ret := api.ToBinary(vals[0], 8)
	for i := 1; i < len(vals); i++ {
		ret = append(api.ToBinary(vals[i], 8), ret...)
	}
	return ret
}

func RotateRight(api frontend.API, bits []frontend.Variable, shift int) []frontend.Variable {
	rotated_bits := append(bits[shift:], bits[:shift]...)
	return rotated_bits
}

func RightShift(api frontend.API, bits []frontend.Variable, shift int) []frontend.Variable {
	shifted_bits := bits[shift:]
	for i := 0; i < shift; i++ {
		shifted_bits = append(shifted_bits, 0)
	}
	return shifted_bits
}

func Sigma0(api frontend.API, val_bits []frontend.Variable) []frontend.Variable {
	v1 := RotateRight(api, val_bits, 7)
	v2 := RotateRight(api, val_bits, 18)
	v3 := RightShift(api, val_bits, 3)
	ret := []frontend.Variable{}
	for i := 0; i < 32; i++ { // Hard-coded 4 bytes
		ret = append(ret, api.Xor(api.Xor(v1[i], v2[i]), v3[i]))
	}
	return ret
}

func Sigma1(api frontend.API, val_bits []frontend.Variable) []frontend.Variable {
	v1 := RotateRight(api, val_bits, 17)
	v2 := RotateRight(api, val_bits, 19)
	v3 := RightShift(api, val_bits, 10)
	ret := []frontend.Variable{}
	for i := 0; i < 32; i++ { // Hard-coded 4 bytes
		ret = append(ret, api.Xor(api.Xor(v1[i], v2[i]), v3[i]))
	}
	return ret
}

func CapSigma0(api frontend.API, val_bits []frontend.Variable) []frontend.Variable {
	v1 := RotateRight(api, val_bits, 2)
	v2 := RotateRight(api, val_bits, 13)
	v3 := RotateRight(api, val_bits, 22)
	ret := []frontend.Variable{}
	for i := 0; i < 32; i++ { // Hard-coded 4 bytes
		ret = append(ret, api.Xor(api.Xor(v1[i], v2[i]), v3[i]))
	}
	return ret
}

func CapSigma1(api frontend.API, val_bits []frontend.Variable) []frontend.Variable {
	v1 := RotateRight(api, val_bits, 6)
	v2 := RotateRight(api, val_bits, 11)
	v3 := RotateRight(api, val_bits, 25)
	ret := []frontend.Variable{}
	for i := 0; i < 32; i++ { // Hard-coded 4 bytes
		ret = append(ret, api.Xor(api.Xor(v1[i], v2[i]), v3[i]))
	}
	return ret
}

func Ch(api frontend.API, x_bits []frontend.Variable, y_bits []frontend.Variable, z_bits []frontend.Variable) []frontend.Variable {
	// will return (x&y) ^ (~x&z)
	ret := []frontend.Variable{}
	for i := 0; i < 32; i++ { // Hard-coded 4 bytes
		new_bit := api.Xor(api.And(x_bits[i], y_bits[i]), api.And(api.Xor(x_bits[i], 1), z_bits[i]))
		ret = append(ret, new_bit)
	}
	return ret
}

// func Maj(api frontend.API, x frontend.Variable, y frontend.Variable, z frontend.Variable) frontend.Variable {
func Maj(api frontend.API, x_bits []frontend.Variable, y_bits []frontend.Variable, z_bits []frontend.Variable) []frontend.Variable {
	// will return (x&y) ^ (x&z) ^ (y&z)
	ret := []frontend.Variable{}
	for i := 0; i < 32; i++ { // Hard-coded 4 bytes
		new_bit := api.Xor(api.Xor(api.And(x_bits[i], y_bits[i]), api.And(x_bits[i], z_bits[i])), api.And(y_bits[i], z_bits[i]))
		ret = append(ret, new_bit)
	}
	return ret
}

