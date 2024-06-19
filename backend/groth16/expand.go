package groth16

import (
	"math/big"

	"github.com/consensys/gnark-crypto/ecc/bn254"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/hash/mimc"
)

// Need initialization after compiling the expansion circuit
var Param Params

type ExpandCircuit struct {
	BigInstance   CommitedRelaxedR1CSVariable
	SmallInstance CommitedRelaxedR1CSVariable
	Z0            []frontend.Variable
	Zi            []frontend.Variable
	Wi            []frontend.Variable
	Com_T         G1Point
	X_Out         frontend.Variable `gnark:",public"`
	Idx           frontend.Variable
	U             frontend.Variable `gnark:",public"`
}

type CommitedRelaxedR1CSVariable struct {
	Com_E G1Point
	Com_W G1Point
	U     frontend.Variable
	X     [3]frontend.Variable
}

type G1Point struct {
	X frontend.Variable
	Y frontend.Variable
	Z frontend.Variable
}

type Params struct {
	M, N, L int
	Pe, Pw  PedersenKey
}

func PointAdd(api frontend.API, p1, p2 *G1Point) *G1Point {
	// Perform the point addition in Jacobian coordinates
	pIsInfinity := api.IsZero(p1.Z)
	qIsInfinity := api.IsZero(p2.Z)
	u1 := api.Mul(p1.X, p2.Z, p2.Z)
	u2 := api.Mul(p2.X, p1.Z, p1.Z)
	s1 := api.Mul(p1.Y, p2.Z, p2.Z, p2.Z)
	s2 := api.Mul(p2.Y, p1.Z, p1.Z, p1.Z)
	h := api.Sub(u2, u1)
	r := api.Sub(s2, s1)
	hIsZero := api.IsZero(h)
	hrIsZero := api.Mul(hIsZero, api.IsZero(r))
	x3 := api.Sub(api.Sub(api.Mul(r, r), api.Mul(h, h, h)), api.Mul(2, u1, h, h))
	y3 := api.Sub(api.Mul(r, api.Sub(api.Mul(u1, h, h), x3)), api.Mul(s1, h, h, h))
	z3 := api.Mul(h, p1.Z, p2.Z)

	tmp := PointDouble(api, p1)

	x3 = api.Select(pIsInfinity, p2.X, x3)
	y3 = api.Select(pIsInfinity, p2.Y, y3)
	z3 = api.Select(pIsInfinity, p2.Z, z3)
	x3 = api.Select(qIsInfinity, p1.X, x3)
	y3 = api.Select(qIsInfinity, p1.Y, y3)
	z3 = api.Select(qIsInfinity, p1.Z, z3)
	x3 = api.Select(hIsZero, tmp.X, x3)
	y3 = api.Select(hIsZero, tmp.Y, y3)
	z3 = api.Select(hIsZero, tmp.Z, z3)
	x3 = api.Select(hrIsZero, 1, x3)
	y3 = api.Select(hrIsZero, 1, y3)
	z3 = api.Select(hrIsZero, 0, z3)
	return &G1Point{X: x3, Y: y3, Z: z3}
}

func PointDouble(api frontend.API, p *G1Point) *G1Point {
	w := api.Mul(3, p.X, p.X)
	s := api.Mul(p.Y, p.Z)
	b := api.Mul(p.X, p.Y, p.Y)
	h := api.Sub(api.Mul(w, w), api.Mul(8, b))
	x3 := api.Mul(2, s, h)
	y3 := api.Sub(api.Mul(w, api.Sub(api.Mul(4, b), h)), api.Mul(8, p.Y, p.Y, p.Y, p.Y))
	z3 := api.Mul(2, p.Y, s)
	return &G1Point{X: x3, Y: y3, Z: z3}
}

func PointScalarMult(api frontend.API, p *G1Point, k frontend.Variable) *G1Point {
	res := &G1Point{X: 1, Y: 1, Z: 0}
	idxs := api.ToBinary(k, 254)
	for i := 253; i >= 0; i-- {
		res = PointDouble(api, res)
		tmp := PointAdd(api, res, p)
		isZero := api.IsZero(idxs[i])
		res.X = api.Select(isZero, res.X, tmp.X)
		res.Y = api.Select(isZero, res.Y, tmp.Y)
		res.Z = api.Select(isZero, res.Z, tmp.Z)
	}
	return res
}

func AssertPointOnCurve(api frontend.API, p *G1Point) {
	x3 := api.Mul(p.X, p.X, p.X)
	y2 := api.Mul(p.Y, p.Y)
	z2 := api.Mul(p.Z, p.Z)
	z6 := api.Mul(z2, z2, z2)
	tmp := api.Add(x3, api.Mul(3, z6))
	api.AssertIsEqual(y2, tmp)
}

func (circuit *ExpandCircuit) Define(api frontend.API) error {
	// Point On Curve Check
	AssertPointOnCurve(api, &circuit.BigInstance.Com_E)
	AssertPointOnCurve(api, &circuit.BigInstance.Com_W)
	AssertPointOnCurve(api, &circuit.SmallInstance.Com_E)
	AssertPointOnCurve(api, &circuit.SmallInstance.Com_W)
	AssertPointOnCurve(api, &circuit.Com_T)

	// Idx = 0
	hasher1, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	hasher1.Write(frontend.Variable(1))
	hasher1.Write(circuit.Z0...)
	z1 := block(api, circuit.Z0, circuit.Wi)
	hasher1.Write(z1)
	emptyIns, err := NewCommittedRelaxedR1CS(Param.N, Param.M, Param.L, Param.Pe, Param.Pw)
	if err != nil {
		return err
	}
	comEJac := bn254.G1Jac{}
	comEJac.FromAffine(&emptyIns.Com_E)
	hasher1.Write(comEJac.X.BigInt(new(big.Int)))
	hasher1.Write(comEJac.Y.BigInt(new(big.Int)))
	hasher1.Write(comEJac.Z.BigInt(new(big.Int)))
	hasher1.Write(emptyIns.U)
	comWJac := bn254.G1Jac{}
	comWJac.FromAffine(&emptyIns.Com_W)
	hasher1.Write(comWJac.X.BigInt(new(big.Int)))
	hasher1.Write(comWJac.Y.BigInt(new(big.Int)))
	hasher1.Write(comWJac.Z.BigInt(new(big.Int)))
	xVar := make([]frontend.Variable, len(emptyIns.X))
	for i := 0; i < len(emptyIns.X); i++ {
		xVar[i] = emptyIns.X[i]
	}
	hasher1.Write(xVar...)
	ret0 := hasher1.Sum()

	// Idx > 0
	hasher2, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	hasher2.Write(circuit.Idx)
	hasher2.Write(circuit.Z0...)
	hasher2.Write(circuit.Zi...)
	hasher2.Write(circuit.BigInstance.Com_E.X)
	hasher2.Write(circuit.BigInstance.Com_E.Y)
	hasher2.Write(circuit.BigInstance.Com_E.Z)
	hasher2.Write(circuit.BigInstance.U)
	hasher2.Write(circuit.BigInstance.Com_W.X)
	hasher2.Write(circuit.BigInstance.Com_W.Y)
	hasher2.Write(circuit.BigInstance.Com_W.Z)
	hasher2.Write(circuit.BigInstance.X[:]...)
	isValid1 := IsEqual(api, circuit.SmallInstance.X, hasher2.Sum())
	isValid2 := IsEqual(api, circuit.SmallInstance.Com_E, emptyIns.Com_E)
	isValid3 := IsEqual(api, circuit.SmallInstance.U, 1)
	newBigInstance, err := FoldVerifyCircuit(api, circuit.BigInstance, circuit.SmallInstance, circuit.Com_T)
	if err != nil {
		return err
	}

	hasher3, err := mimc.NewMiMC(api)
	if err != nil {
		return err
	}
	hasher3.Write(api.Add(circuit.Idx, 1))
	hasher3.Write(circuit.Z0...)
	newZ := block(api, circuit.Zi, circuit.Wi)
	hasher3.Write(newZ...)
	hasher3.Write(newBigInstance.Com_E.X)
	hasher3.Write(newBigInstance.Com_E.Y)
	hasher3.Write(newBigInstance.Com_E.Z)
	hasher3.Write(newBigInstance.U)
	hasher3.Write(newBigInstance.Com_W.X)
	hasher3.Write(newBigInstance.Com_W.Y)
	hasher3.Write(newBigInstance.Com_W.Z)
	hasher3.Write(newBigInstance.X[:]...)
	ret1 := hasher3.Sum()
	isValid4 := api.Select(api.IsZero(circuit.Idx), IsEqual(api, circuit.X_Out, ret0), IsEqual(api, circuit.X_Out, ret1))
	api.AssertIsEqual(api.Add(isValid1, isValid2, isValid3, isValid4), 4)
	return nil
}

func FoldVerifyCircuit(api frontend.API, bigInstance, smallInstance CommitedRelaxedR1CSVariable, comT G1Point) (CommitedRelaxedR1CSVariable, error) {
	hasher, err := mimc.NewMiMC(api)
	if err != nil {
		return CommitedRelaxedR1CSVariable{}, err
	}
	hasher.Write(comT.X, comT.Y, comT.Z)
	r := hasher.Sum()
	rSquare := api.Mul(r, r)
	rt := PointScalarMult(api, &comT, r)
	rre2 := PointScalarMult(api, &smallInstance.Com_E, rSquare)
	new_com_e := PointAdd(api, &bigInstance.Com_E, PointAdd(api, rt, rre2))
	new_u := api.Add(bigInstance.U, api.Mul(r, smallInstance.U))
	rw2 := PointScalarMult(api, &smallInstance.Com_W, rSquare)
	new_com_w := PointAdd(api, &bigInstance.Com_W, rw2)
	new_x := [3]frontend.Variable{}
	new_x[0] = api.Add(bigInstance.X[0], api.Mul(r, smallInstance.X[0]))
	new_x[1] = api.Add(bigInstance.X[1], api.Mul(r, smallInstance.X[1]))
	new_x[2] = api.Add(bigInstance.X[2], api.Mul(r, smallInstance.X[2]))
	return CommitedRelaxedR1CSVariable{Com_E: *new_com_e, Com_W: *new_com_w, U: new_u, X: new_x}, nil
}

func SHA256PlaceHolder(api frontend.API, h, x []frontend.Variable) []frontend.Variable {
	return x
}

func IsEqual(api frontend.API, a frontend.Variable, b frontend.Variable) frontend.Variable {
	return api.IsZero(api.Sub(a, b))
}
