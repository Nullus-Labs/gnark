package groth16

import (
	"crypto/rand"
	"errors"
	"math/big"
	"sync"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr"
	"github.com/consensys/gnark-crypto/ecc/bn254/fr/mimc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/constraint"
	cs "github.com/consensys/gnark/constraint/bn254"
)

type CommitedRelaxedR1CS struct {
	// Instance
	Com_E bn254.G1Affine
	U     fr.Element
	Com_W bn254.G1Affine
	X     []fr.Element // Length l
	// Witness
	E      []fr.Element // Length m
	W      []fr.Element // Length m-l-1
	Rand_E fr.Element
	Rand_W fr.Element
}

func NewCommittedRelaxedR1CS(n, m, l int, pk_e, pk_w PedersenKey) (*CommitedRelaxedR1CS, error) {
	rand_e, rand_w := fr.NewElement(0), fr.NewElement(0)
	e, w := makeZeroElements(n), makeZeroElements(m-l-1)
	com_e, err := pk_e.Commit(e, rand_e)
	if err != nil {
		return nil, err
	}
	com_w, err := pk_w.Commit(w, rand_w)
	if err != nil {
		return nil, err
	}
	return &CommitedRelaxedR1CS{
		Com_E:  com_e,
		Com_W:  com_w,
		E:      e,
		W:      w,
		X:      makeZeroElements(l),
		U:      fr.NewElement(0),
		Rand_E: rand_e,
		Rand_W: rand_w,
	}, nil
}

// witness = [publicWires | secretWires] (without the ONE_WIRE !)
func NewCommittedRelaxedR1CSFromInstance(r1cs *cs.R1CS, witness fr.Vector, pk_e, pk_w PedersenKey) (*CommitedRelaxedR1CS, error) {
	new_witness := make([]fr.Element, len(witness)+1)
	nbPublic := r1cs.GetNbPublicVariables()
	copy(new_witness[:nbPublic], witness[:nbPublic])
	copy(new_witness[nbPublic+1:], witness[nbPublic:])
	new_witness[nbPublic] = fr.NewElement(1)
	r1cs.AddPublicVariable("u")
	// solve the R1CS and compute the a, b, c vectors
	a := make([]fr.Element, len(r1cs.Constraints))
	b := make([]fr.Element, len(r1cs.Constraints))
	c := make([]fr.Element, len(r1cs.Constraints))

	// wirevalues  [publicWires | secretWires | internalWires ]
	var wireValues []fr.Element
	opt, err := backend.NewProverConfig()
	if err != nil {
		return nil, err
	}
	if wireValues, err = r1cs.Solve(new_witness, a, b, c, opt); err != nil {
		return nil, err
	}
	x := wireValues[:r1cs.GetNbPublicVariables()-1]
	w := wireValues[r1cs.GetNbPublicVariables():]
	rand_e, err := rand.Int(rand.Reader, fr.Modulus())
	if err != nil {
		return nil, err
	}
	rand_w, err := rand.Int(rand.Reader, fr.Modulus())
	if err != nil {
		return nil, err
	}
	rand_e_fr, rand_w_fr := fr.NewElement(0), fr.NewElement(0)
	rand_e_fr.SetBigInt(rand_e)
	rand_w_fr.SetBigInt(rand_w)

	e := makeZeroElements(len(r1cs.Constraints))
	com_e, err := pk_e.Commit(e, rand_e_fr)
	if err != nil {
		panic(err)
	}
	com_w, err := pk_w.Commit(w, rand_w_fr)
	if err != nil {
		panic(err)
	}

	u := wireValues[r1cs.GetNbPublicVariables()-1]
	one := fr.NewElement(1)
	if !u.Equal(&one) {
		return nil, errors.New("u is not equal to 1")
	}
	return &CommitedRelaxedR1CS{
		Com_E:  com_e,
		Com_W:  com_w,
		E:      e,
		W:      w,
		X:      x,
		U:      u,
		Rand_E: rand_e_fr,
		Rand_W: rand_w_fr,
	}, nil
}

// Z = (x, u, w)
func (primary *CommitedRelaxedR1CS) FoldProve(r1cs *cs.R1CS, secondary *CommitedRelaxedR1CS, pk_e PedersenKey) (*CommitedRelaxedR1CS, bn254.G1Affine, error) {
	// Compute T
	z1 := append(append(primary.X, primary.U), primary.W...)
	z2 := append(append(secondary.X, secondary.U), secondary.W...)
	az1, az2, bz1, bz2, cz1, cz2 := parallelMatrixMul(r1cs, z1, z2)
	t1 := batchAdd(batchMul(az1, bz2), batchMul(az2, bz1))
	t2 := batchAdd(scalarMul(primary.U, cz2), scalarMul(secondary.U, cz1))
	t := batchSub(t1, t2)

	// Commit T
	rand_t, err := rand.Int(rand.Reader, fr.Modulus())
	if err != nil {
		return nil, bn254.G1Affine{}, err
	}
	rand_t_fr := fr.NewElement(0)
	rand_t_fr.SetBigInt(rand_t)

	com_t, err := pk_e.Commit(t, rand_t_fr)
	if err != nil {
		return nil, bn254.G1Affine{}, err
	}

	//Sample random r
	com_t_bytes := com_t.Bytes()
	r_val := mimcHash(com_t_bytes[:])
	
	// Compute folded instance
	new_com_e := bn254.G1Affine{}
	new_com_e.Set(&primary.Com_E)
	rt := bn254.G1Affine{}
	rt.ScalarMultiplication(&com_t, r_val.BigInt(new(big.Int)))
	rsquare := fr.NewElement(0)
	rsquare.Square(&r_val)
	rsquare_e2 := bn254.G1Affine{}
	rsquare_e2.ScalarMultiplication(&secondary.Com_E, rsquare.BigInt(new(big.Int)))
	new_com_e.Add(&new_com_e, &rt)
	new_com_e.Add(&new_com_e, &rsquare_e2)

	new_u := fr.NewElement(0)
	ru2 := fr.NewElement(0)
	ru2.Mul(&r_val, &secondary.U)
	new_u.Add(&primary.U, &ru2)

	new_com_w := bn254.G1Affine{}
	new_com_w.Set(&primary.Com_W)
	rw := bn254.G1Affine{}
	rw.ScalarMultiplication(&secondary.Com_W, r_val.BigInt(new(big.Int)))
	new_com_w.Add(&new_com_w, &rw)

	new_x := make([]fr.Element, len(primary.X))
	for i := range new_x {
		new_x[i] = fr.NewElement(0)
		rx2 := fr.NewElement(0)
		rx2.Mul(&r_val, &secondary.X[i])
		new_x[i].Add(&primary.X[i], &rx2)
	}

	new_e := make([]fr.Element, len(primary.E))
	for i := range new_e {
		new_e[i] = fr.NewElement(0)
		rt := fr.NewElement(0)
		rt.Mul(&r_val, &t[i])
		rsquare_e2 := fr.NewElement(0)
		rsquare_e2.Mul(&rsquare, &secondary.E[i])
		new_e[i].Add(&primary.E[i], &rt)
		new_e[i].Add(&new_e[i], &rsquare_e2)
	}

	new_rand_e := fr.NewElement(0)
	new_rand_e.Mul(&r_val, &rand_t_fr)
	new_rand_e.Add(&new_rand_e, &primary.Rand_E)
	r_rand_e2 := fr.NewElement(0)
	r_rand_e2.Mul(&rsquare, &secondary.Rand_E)
	new_rand_e.Add(&new_rand_e, &r_rand_e2)

	new_w := make([]fr.Element, len(primary.W))
	for i := range new_w {
		new_w[i] = fr.NewElement(0)
		rw2 := fr.NewElement(0)
		rw2.Mul(&r_val, &secondary.W[i])
		new_w[i].Add(&primary.W[i], &rw2)
	}

	new_rand_w := fr.NewElement(0)
	new_rand_w.Mul(&r_val, &secondary.Rand_W)
	new_rand_w.Add(&new_rand_w, &primary.Rand_W)

	return &CommitedRelaxedR1CS{
		Com_E:  new_com_e,
		U:      new_u,
		Com_W:  new_com_w,
		X:      new_x,
		E:      new_e,
		W:      new_w,
		Rand_E: new_rand_e,
		Rand_W: new_rand_w,
	}, com_t, nil
}

// Z = (x, u, w)
func (primary *CommitedRelaxedR1CS) FoldVerify(r1cs *cs.R1CS, secondary *CommitedRelaxedR1CS, com_t bn254.G1Affine) (*CommitedRelaxedR1CS, error) {
	//Sample random r
	com_t_bytes := com_t.Bytes()
	r_val := mimcHash(com_t_bytes[:])
	
	// Compute folded instance
	new_com_e := bn254.G1Affine{}
	new_com_e.Set(&primary.Com_E)
	rt := bn254.G1Affine{}
	rt.ScalarMultiplication(&com_t, r_val.BigInt(new(big.Int)))
	rsquare := fr.NewElement(0)
	rsquare.Square(&r_val)
	rsquare_e2 := bn254.G1Affine{}
	rsquare_e2.ScalarMultiplication(&secondary.Com_E, rsquare.BigInt(new(big.Int)))
	new_com_e.Add(&new_com_e, &rt)
	new_com_e.Add(&new_com_e, &rsquare_e2)

	new_u := fr.NewElement(0)
	ru2 := fr.NewElement(0)
	ru2.Mul(&r_val, &secondary.U)
	new_u.Add(&primary.U, &ru2)

	new_com_w := bn254.G1Affine{}
	new_com_w.Set(&primary.Com_W)
	rw := bn254.G1Affine{}
	rw.ScalarMultiplication(&secondary.Com_W, r_val.BigInt(new(big.Int)))
	new_com_w.Add(&new_com_w, &rw)

	new_x := make([]fr.Element, len(primary.X))
	for i := range new_x {
		new_x[i] = fr.NewElement(0)
		rx2 := fr.NewElement(0)
		rx2.Mul(&r_val, &secondary.X[i])
		new_x[i].Add(&primary.X[i], &rx2)
	}


	return &CommitedRelaxedR1CS{
		Com_E:  new_com_e,
		U:      new_u,
		Com_W:  new_com_w,
		X:      new_x,
	}, nil
}

// parallelMatrixMul performs parallel matrix multiplication on the constraints and vectors z1 and z2.
func parallelMatrixMul(r1cs *cs.R1CS, z1 []fr.Element, z2 []fr.Element) ([]fr.Element, []fr.Element, []fr.Element, []fr.Element, []fr.Element, []fr.Element) {
	n := len(r1cs.Constraints)
	az1, az2, bz1, bz2, cz1, cz2 := make([]fr.Element, n), make([]fr.Element, n), make([]fr.Element, n), make([]fr.Element, n), make([]fr.Element, n), make([]fr.Element, n)

	var wg sync.WaitGroup
	wg.Add(n * 6) // Six computations per constraint

	for i, c := range r1cs.Constraints {
		go func(i int, c constraint.R1C) {
			defer wg.Done()
			az1[i] = accumulateLinearExp(r1cs, c.L, z1)
		}(i, c)

		go func(i int, c constraint.R1C) {
			defer wg.Done()
			az2[i] = accumulateLinearExp(r1cs, c.L, z2)
		}(i, c)

		go func(i int, c constraint.R1C) {
			defer wg.Done()
			bz1[i] = accumulateLinearExp(r1cs, c.R, z1)
		}(i, c)

		go func(i int, c constraint.R1C) {
			defer wg.Done()
			bz2[i] = accumulateLinearExp(r1cs, c.R, z2)
		}(i, c)

		go func(i int, c constraint.R1C) {
			defer wg.Done()
			cz1[i] = accumulateLinearExp(r1cs, c.O, z1)
		}(i, c)

		go func(i int, c constraint.R1C) {
			defer wg.Done()
			cz2[i] = accumulateLinearExp(r1cs, c.O, z2)
		}(i, c)
	}

	wg.Wait() // Wait for all goroutines to finish

	return az1, az2, bz1, bz2, cz1, cz2
}

func batchMul(a, b []fr.Element) []fr.Element {
	if len(a) != len(b) {
		panic("batchMul: vectors not of the same length")
	}
	res := makeZeroElements(len(a))
	for i := range a {
		res[i].Mul(&a[i], &b[i])
	}
	return res
}

func scalarMul(u fr.Element, a []fr.Element) []fr.Element {
	res := makeZeroElements(len(a))
	for i := range a {
		res[i].Mul(&u, &a[i])
	}
	return res
}

func batchAdd(a, b []fr.Element) []fr.Element {
	if len(a) != len(b) {
		panic("batchAdd: vectors not of the same length")
	}
	res := makeZeroElements(len(a))
	for i := range a {
		res[i].Add(&a[i], &b[i])
	}
	return res
}

func batchSub(a, b []fr.Element) []fr.Element {
	if len(a) != len(b) {
		panic("batchSub: vectors not of the same length")
	}
	res := makeZeroElements(len(a))
	for i := range a {
		res[i].Sub(&a[i], &b[i])
	}
	return res
}

func accumulateLinearExp(r1cs *cs.R1CS, l constraint.LinearExpression, z []fr.Element) fr.Element {
	r := new(fr.Element)
	r.SetZero()
	for _, t := range l {
		cID := t.CoeffID()

		if t.IsConstant() {
			// needed for logs, we may want to not put this in the hot path if we need to
			// optimize constraint system solver further.
			r.Add(r, &r1cs.Coefficients[cID])
			continue
		}

		vID := t.WireID()
		switch cID {
		case constraint.CoeffIdZero:
			continue
		case constraint.CoeffIdOne:
			r.Add(r, &z[vID])
		case constraint.CoeffIdTwo:
			var res fr.Element
			res.Double(&z[vID])
			r.Add(r, &res)
		case constraint.CoeffIdMinusOne:
			r.Sub(r, &z[vID])
		default:
			var res fr.Element
			res.Mul(&r1cs.Coefficients[cID], &z[vID])
			r.Add(r, &res)
		}
	}
	return *r
}

func makeZeroElements(n int) []fr.Element {
	res := make([]fr.Element, n)
	for i := range res {
		res[i] = fr.NewElement(0)
	}
	return res
}

func mimcHash(x []byte) fr.Element {
	h := mimc.NewMiMC()
	res := fr.NewElement(0)
	res.SetBytes(h.Sum(x))
	return res
}