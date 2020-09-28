package bn256

import (
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"math/big"
	"math/bits"

	"golang.org/x/crypto/hkdf"
)

type gfP [4]uint64

func newGFp(x int64) (out *gfP) {
	if x >= 0 {
		out = &gfP{uint64(x)}
	} else {
		out = &gfP{uint64(-x)}
		gfpNeg(out, out)
	}

	montEncode(out, out)
	return out
}

// hashToBase implements hashing a message to an element of the field.
//
// L = ceil((256+128)/8)=48, ctr = 0, i = 1
func hashToBase(msg, dst []byte) *gfP {
	var t [48]byte
	info := []byte{'H', '2', 'C', byte(0), byte(1)}
	r := hkdf.New(sha256.New, msg, dst, info)
	if _, err := r.Read(t[:]); err != nil {
		panic(err)
	}
	var x big.Int
	v := x.SetBytes(t[:]).Mod(&x, p).Bytes()
	v32 := [32]byte{}
	for i := len(v) - 1; i >= 0; i-- {
		v32[len(v)-1-i] = v[i]
	}
	u := &gfP{
		binary.LittleEndian.Uint64(v32[0*8 : 1*8]),
		binary.LittleEndian.Uint64(v32[1*8 : 2*8]),
		binary.LittleEndian.Uint64(v32[2*8 : 3*8]),
		binary.LittleEndian.Uint64(v32[3*8 : 4*8]),
	}
	montEncode(u, u)
	return u
}

func (e *gfP) String() string {
	return fmt.Sprintf("%16.16x%16.16x%16.16x%16.16x", e[3], e[2], e[1], e[0])
}

func (e *gfP) Set(f *gfP) {
	e[0] = f[0]
	e[1] = f[1]
	e[2] = f[2]
	e[3] = f[3]
}

func (e *gfP) exp(f *gfP, bits [4]uint64) {
	sum, power := &gfP{}, &gfP{}
	sum.Set(rN1)
	power.Set(f)

	for word := 0; word < 4; word++ {
		for bit := uint(0); bit < 64; bit++ {
			if (bits[word]>>bit)&1 == 1 {
				gfpMul(sum, sum, power)
			}
			gfpMul(power, power, power)
		}
	}

	gfpMul(sum, sum, r3)
	e.Set(sum)
}

func (e *gfP) Invert(f *gfP) {
	e.exp(f, pMinus2)
}

func (e *gfP) Sqrt(f *gfP) {
	// Since p = 4k+3, then e = f^(k+1) is a root of f.
	e.exp(f, pPlus1Over4)
}

func (e *gfP) Marshal(out []byte) {
	for w := uint(0); w < 4; w++ {
		for b := uint(0); b < 8; b++ {
			out[8*w+b] = byte(e[3-w] >> (56 - 8*b))
		}
	}
}

func (e *gfP) Unmarshal(in []byte) {
	for w := uint(0); w < 4; w++ {
		e[3-w] = 0
		for b := uint(0); b < 8; b++ {
			e[3-w] += uint64(in[8*w+b]) << (56 - 8*b)
		}
	}
}

func montEncode(c, a *gfP) { gfpMul(c, a, r2) }
func montDecode(c, a *gfP) { gfpMul(c, a, &gfP{1}) }

func sign0(e *gfP) int {
	x := &gfP{}
	montDecode(x, e)
	for w := 3; w >= 0; w-- {
		if x[w] > pMinus1Over2[w] {
			return 1
		} else if x[w] < pMinus1Over2[w] {
			return -1
		}
	}
	return 1
}

func legendre(e *gfP) int {
	f := &gfP{}
	// Since p = 4k+3, then e^(2k+1) is the Legendre symbol of e.
	f.exp(e, pMinus1Over2)

	montDecode(f, f)

	if *f != [4]uint64{} {
		return 2*int(f[0]&1) - 1
	}

	return 0
}

func isZero(a *gfP) bool {
	return (a[0] | a[1] | a[2] | a[3]) == 0
}

func isEven(a *gfP) bool {
	return a[0]&1 == 0
}

func div2(a *gfP) {
	a[0] = a[0]>>1 | a[1]<<63
	a[1] = a[1]>>1 | a[2]<<63
	a[2] = a[2]>>1 | a[3]<<63
	a[3] = a[3] >> 1
}

func (e *gfP) addNocarry(f *gfP) {
	carry := uint64(0)
	e[0], carry = bits.Add64(e[0], f[0], carry)
	e[1], carry = bits.Add64(e[1], f[1], carry)
	e[2], carry = bits.Add64(e[2], f[2], carry)
	e[3], _ = bits.Add64(e[3], f[3], carry)
}

func (e *gfP) subNoborrow(f *gfP) {
	borrow := uint64(0)
	e[0], borrow = bits.Sub64(e[0], f[0], borrow)
	e[1], borrow = bits.Sub64(e[1], f[1], borrow)
	e[2], borrow = bits.Sub64(e[2], f[2], borrow)
	e[3], _ = bits.Sub64(e[3], f[3], borrow)
}

func gte(a, b *gfP) bool {
	// subtract b from a. If no borrow occures then a >= b
	borrow := uint64(0)
	_, borrow = bits.Sub64(a[0], b[0], borrow)
	_, borrow = bits.Sub64(a[1], b[1], borrow)
	_, borrow = bits.Sub64(a[2], b[2], borrow)
	_, borrow = bits.Sub64(a[3], b[3], borrow)

	return borrow == 0
}

// Performs inversion of the field element using binary EEA.
// If element is zero (no inverse exists) then set `e` to zero
func (e *gfP) InvertVariableTime(f *gfP) {
	if isZero(f) {
		e.Set(&gfP{0, 0, 0, 0})
		return
	}

	// Guajardo Kumar Paar Pelzl
	// Efficient Software-Implementation of Finite Fields with Applications to Cryptography
	// Algorithm 16 (BEA for Inversion in Fp)

	one := gfP{1, 0, 0, 0}

	u, b := gfP{}, gfP{}
	u.Set(f)
	b.Set(r2)

	v := gfP(p2)
	c := gfP{0, 0, 0, 0}
	modulus := gfP(p2)

	for u != one && v != one {
		// while u is even
		for isEven(&u) {
			div2(&u)
			if !isEven(&b) {
				// we will not overflow a modulus here,
				// so we can use specialized function
				// do perform addition without reduction
				b.addNocarry(&modulus)
			}
			div2(&b)
		}

		// while v is even
		for isEven(&v) {
			div2(&v)
			if !isEven(&c) {
				// we will not overflow a modulus here,
				// so we can use specialized function
				// do perform addition without reduction
				c.addNocarry(&modulus)
			} else {

			}
			div2(&c)
		}

		if gte(&u, &v) {
			u.subNoborrow(&v)
			gfpSub(&b, &b, &c)
		} else {
			v.subNoborrow(&u)
			gfpSub(&c, &c, &b)
		}
	}

	if u == one {
		e.Set(&b)
	} else {
		e.Set(&c)
	}
}
