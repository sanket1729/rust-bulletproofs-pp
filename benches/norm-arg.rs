#![allow(non_snake_case)]

use merlin::Transcript;
use rand::thread_rng;
use secp256kfun::{g, hash::Tagged, s, Point, G};
extern crate sha2;
use sha2::{digest::Digest, Sha256};

use secp256kfun::{marker::*, Scalar};

type PubScalarZ = Scalar<Public, Zero>;
type PubScalarNz = Scalar<Public, NonZero>;

extern crate merlin;

/// Base generators used in the norm argument.
/// Unlike inner product arguments, G and H might not be of the
/// same length.
#[derive(Clone, Debug)]
pub struct BaseGens {
    /// The points Vec<G>
    pub G_vec: Vec<Point<Jacobian>>,
    /// The points H
    pub H_vec: Vec<Point<Jacobian>>,
}

impl BaseGens {
    /// Create a new base generator with the given G and H.
    pub fn new(num_g: u32, num_h: u32) -> Self {
        // generate a set of generators for G
        fn gen_tagged_points(n: u32, tag: &str) -> Vec<Point<Jacobian>> {
            let mut gs = Vec::with_capacity(n as usize);
            let mut i: u64 = 0;
            while gs.len() < n as usize {
                loop {
                    i = i + 1;
                    let mut hash_x = Tagged::tagged(&Sha256::default(), &[tag.as_bytes(), b"x"].concat());
                    hash_x.update(&i.to_be_bytes());
                    let gen_x = hash_x.finalize();
                    let mut hash_y =
                        sha2::Sha256::default().tagged(&[tag.as_bytes(), b"y"].concat());
                    hash_y.update(&i.to_be_bytes());
                    let gen_y = hash_y.finalize();

                    let mut bytes = [0u8; 33];
                    bytes[1..].copy_from_slice(&gen_x);
                    bytes[0] = 2u8 + (gen_y[0] & 1u8);
                    match Point::from_bytes(bytes) {
                        Some(g) => {
                            gs.push(g.mark::<Jacobian>());
                            break;
                        }
                        None => continue,
                    }
                }
            }
            gs
        }

        let gs = gen_tagged_points(num_g, "BulletProofs/G");
        let hs = gen_tagged_points(num_h, "BulletProofs/H");
        Self {
            G_vec: gs,
            H_vec: hs,
        }
    }
}

/// A Schnorr signature.
#[derive(Debug, Clone)]
pub struct NormProof {
    /// Vector of points X_i that used during norm recursion
    pub x_vec: Vec<Point>,
    /// Vector of points R_i that used during norm recursion
    pub r_vec: Vec<Point>,
    /// The norm vector reducing the recursion to 1.
    pub n: PubScalarZ,
    /// The l value
    pub l: PubScalarZ,
}

/// Compute the inner product of two vectors <l, c>.
fn inner_product<'a, A, B>(l_vec: &A, c_vec: &B) -> PubScalarZ
where
    A: Iterator<Item = &'a PubScalarZ> + Clone,
    B: Iterator<Item = &'a PubScalarZ> + Clone,
{
    let mut res = s!(0);
    for (a, b) in l_vec.clone().into_iter().zip(c_vec.clone().into_iter()) {
        res = s!(res + a * b);
    }
    res.mark::<Public>()
}

/// Compute the q-weighted inner product of two vectors.
fn weighted_inner_product<'a, A, B>(a_iter: &A, b_iter: &B, q: PubScalarNz) -> PubScalarZ
where
    A: Iterator<Item = &'a PubScalarZ> + Clone,
    B: Iterator<Item = &'a PubScalarZ> + Clone,
{
    let mut res = s!(0);
    let mut q_pow = s!(1).mark::<Zero>();
    for (a, b) in a_iter.clone().into_iter().zip(b_iter.clone().into_iter()) {
        q_pow = s!(q_pow * q);
        res = s!(res + a * b * q_pow);
    }
    res.mark::<Public>()
}

// /// Compute the q-weighted inner product of two vectors.
// fn q_weighted_inner_product(a: &[Scalar], b: &[Scalar]) -> Scalar {
//     a.iter().zip(b).map(|(a, b)| a * b).sum()
// }

/// Compute v*G + <G_vec, n> + <H_vec, l>
fn bp_comm<'a, A, B>(
    v: Scalar<Public, Zero>,
    G_vec: &A,
    H_vec: &A,
    n: &B,
    l: &B,
) -> Point<Jacobian, Public, Zero>
where
    A: Iterator<Item = &'a Point<Jacobian>> + Clone,
    B: Iterator<Item = &'a PubScalarZ> + Clone,
{
    let mut res = g!(v * G);
    for (g, n) in G_vec.clone().into_iter().zip(n.clone().into_iter()) {
        res = g!(res + n * g);
    }
    for (h, l) in H_vec.clone().into_iter().zip(l.clone().into_iter()) {
        res = g!(res + l * h);
    }
    res
}

/// Compute R + r*<l, G>
fn point_inner_product<'a, A, B>(Gs: &A, l: &B) -> Point<Jacobian, Public, Zero>
where
    A: Iterator<Item = &'a Point<Jacobian>> + Clone,
    B: Iterator<Item = &'a PubScalarZ> + Clone,
{
    let mut res = Point::zero().mark::<Jacobian>();
    for (g, l) in Gs.clone().into_iter().zip(l.clone().into_iter()) {
        res = g!(res + l * g);
    }
    res
}

// Compute a scalar challenge from a transcript.
fn scalar_challenge(t: &mut merlin::Transcript) -> PubScalarNz {
    let mut dest = [0u8; 32];
    t.challenge_bytes(b"e", &mut dest);
    let e = Scalar::from_bytes(dest).unwrap();
    let e = e.mark::<Public>();
    e.mark::<NonZero>().unwrap()
}

impl NormProof {
    /// Compute v = |w|^2_q + <l, q>
    pub(crate) fn v(
        w_vec: &[PubScalarZ],
        l_vec: &[PubScalarZ],
        c_vec: &[PubScalarZ],
        q: PubScalarNz,
    ) -> Scalar<Public, Zero> {
        let w_sq = weighted_inner_product(&w_vec.iter(), &w_vec.iter(), q);
        // Compute <l, c>
        let l_c = inner_product(&l_vec.iter(), &c_vec.iter());
        // Compute v = w*w*q + <l, c>
        s!(w_sq + l_c).mark::<Public>()
    }

    /// Prove that w^2 + <l, c> = v
    /// Use the challenge as r and compute q = r^2
    pub fn prove(
        transcript: &mut merlin::Transcript,
        mut gens: BaseGens,
        mut w: Vec<Scalar<Public, Zero>>,
        mut l: Vec<Scalar<Public, Zero>>,
        mut c: Vec<Scalar<Public, Zero>>,
        mut r: Scalar<Public>,
    ) -> Self {
        let mut w_n = w.len();
        let mut l_n = l.len();

        let mut Gs = &mut gens.G_vec[..];
        let mut Hs = &mut gens.H_vec[..];

        let mut w = &mut w[..];
        let mut l = &mut l[..];
        let mut c = &mut c[..];

        assert_eq!(Gs.len(), w_n);
        assert_eq!(c.len(), l_n);
        assert_eq!(Hs.len(), l_n);
        assert!(w_n.is_power_of_two());
        assert!(l_n.is_power_of_two());

        let ln_n = std::cmp::max(l_n, w_n).next_power_of_two();
        let mut X_vec = Vec::with_capacity(ln_n);
        let mut R_vec = Vec::with_capacity(ln_n);
        let mut q = s!(r * r).mark::<Public>();

        let v_init = Self::v(w, l, c, q);
        let mut v_final = v_init;

        fn alter_iter<T>(
            a: &mut [T],
        ) -> (
            impl Iterator<Item = &T> + Clone,
            impl Iterator<Item = &T> + Clone,
        ) {
            let iter0 = a.iter().step_by(2).map(|x| &*x);
            let iter1 = a.iter().skip(1).step_by(2).map(|x| &*x);
            (iter0, iter1)
        }

        while w_n != 1 || l_n != 1 {
            let (r_inv, r_old, q_old, q_sq, e) = {
                let (w0, w1) = alter_iter(w);
                let (g0, g1) = alter_iter(Gs);

                let (l0, l1) = alter_iter(l);
                let (c0, c1) = alter_iter(c);
                let (h0, h1) = alter_iter(Hs);

                let q_sq = s!(q * q).mark::<Public>();
                let r_inv = r.invert().mark::<Public>();
                let X_v0 = inner_product(&c0, &l1);
                let X_v1 = inner_product(&c1, &l0);
                let X_v2 = weighted_inner_product(&w0, &w1, q_sq);
                let X_v = &s!(X_v0 + X_v1 + 2 * r_inv * X_v2);
                // assert_eq!(*X_v, {let wa = w0[0]; let wb = w1[0]; s!(2*wa *wb*q_sq*r_inv)});

                let mut X = g!(X_v * G);
                // X = X + <g0, w1>*r + <g1, w0>/r + <h0, l1> + <h1, l0>
                let X1 = point_inner_product(&g0, &w1);
                let X2 = point_inner_product(&g1, &w0);
                let X3 = point_inner_product(&h0, &l1);
                let X4 = point_inner_product(&h1, &l0);
                X = g!(X + r * X1 + r_inv * X2 + X3 + X4);

                let R_v_0 = inner_product(&c1, &l1);
                let R_v_1 = weighted_inner_product(&w1, &w1, q_sq);
                let R_v = s!(R_v_0 + R_v_1).mark::<Public>();
                // assert_eq!(R_v, {let wa = w1[0]; s!(wa *wa*q_sq)});
                let R = bp_comm(R_v, &g1, &h1, &w1, &l1);

                let X = X.mark::<NonZero>().unwrap().normalize();
                let R = R.mark::<NonZero>().unwrap().normalize();

                transcript.append_message(b"L", &X.to_bytes());
                transcript.append_message(b"R", &R.to_bytes());

                X_vec.push(X);
                R_vec.push(R);

                // let e = scalar_challenge(transcript);
                let e = s!(2).mark::<Public>();
                (r_inv, r, q, q_sq, e)
            };
            if w_n > 1 {
                let mut i = 0;
                while i < w_n {
                    let (wl, wr, gl, gr) = (w[i], w[i + 1], Gs[i], Gs[i + 1]);
                    w[i/2] = s!(r_inv * wl + e * wr).mark::<Public>();
                    Gs[i/2] = g!(r * gl + e * gr).mark::<NonZero>().unwrap();
                    i = i + 2;
                }
            }

            if l_n > 1 {
                let mut i = 0;
                while i < l_n {
                    let (cl, cr, hl, hr) = (c[i], c[i + 1], Hs[i], Hs[i + 1]);
                    let (ll, lr) = (l[i], l[i + 1]);
                    c[i/2] = s!(cl + e * cr).mark::<Public>();
                    l[i/2] = s!(ll + e * lr).mark::<Public>();
                    Hs[i/2] = g!(hl + e * hr).mark::<NonZero>().unwrap();
                    i += 2;
                }
            }
            w_n = (w_n + 1) / 2; // Adding 1 ensures that stop at 1 and don't go to zero.
            l_n = (l_n + 1) / 2;
            w = &mut w[..w_n];
            Gs = &mut Gs[..w_n];
            l = &mut l[..l_n];
            c = &mut c[..l_n];
            Hs = &mut Hs[..l_n];
            r = q_old;
            q = q_sq;
        }

        Self {
            x_vec: X_vec,
            r_vec: R_vec,
            n: w[0],
            l: l[0],
        }
    }

    fn g_vec_r_coeffs(n: usize) -> Vec<u64> {
        let lg_n = log(n);
        let mut r_factors = Vec::with_capacity(n);
        r_factors.push(0u64);

        for i in 1..n {
            let lg_i = log(i);
            let k = 1 << lg_i;

            let r_val = 1 << lg_i;
            let r_not_last_set_bit = r_factors[i - k];
            r_factors.push(r_val + r_not_last_set_bit);
        }
        r_factors
    }

    fn s_vec(n: usize, challenges: &[PubScalarNz]) -> Vec<PubScalarZ> {
        let mut s = Vec::with_capacity(n);
        let lg_n = log(n);
        s.push(s!(1).mark::<Public>().mark::<Zero>());
        for i in 1..n {
            let lg_i = log(i);
            let k = 1 << lg_i;
            // so u_{lg(i)+1} = is indexed by (lg_n-1) - lg_i
            let u_val = challenges[lg_i];
            let u_not_last_set_bit = s[i - k];
            s.push(
                s!(u_not_last_set_bit * u_val)
                    .mark::<Public>()
                    .mark::<Zero>(),
            );
        }
        s
    }

    // Get the scalars to be used in verification in multi scalar exponentiation.
    fn verification_scalars(
        &self,
        t: &mut merlin::Transcript,
        r: PubScalarNz,
        g_n: usize,
        h_n: usize,
    ) -> (Vec<PubScalarNz>, Vec<PubScalarZ>, Vec<PubScalarZ>) {
        let mut challenges = Vec::with_capacity(self.x_vec.len());
        for (X, R) in self.x_vec.iter().zip(self.r_vec.iter()) {
            t.append_message(b"L", &X.to_bytes());
            t.append_message(b"R", &R.to_bytes());
            let e = s!(2).mark::<Public>();
            // challenges.push(scalar_challenge(t));
            challenges.push(e);
        }

        // Similar to s used in dalek crypto bp implementation, but modified for bp++
        let mut s_g = Self::s_vec(g_n, &challenges);
        let s_h = Self::s_vec(h_n, &challenges);
        let r_pow_perm = Self::g_vec_r_coeffs(g_n);

        // Compute g_n powers of q
        let mut r_pows = Vec::with_capacity(g_n);
        r_pows.push(s!(1).mark::<Public>());
        for i in 1..g_n {
            let last = r_pows[i - 1];
            r_pows.push(s!(last * r).mark::<Public>());
        }
        // Compute s_g * q_pow_perm
        for i in 0..g_n {
            let (s_g_i, q_pow_perm_i) = (s_g[i], r_pows[g_n - 1 - r_pow_perm[i] as usize]);
            s_g[i] = s!(s_g_i * q_pow_perm_i).mark::<Public>();
        }
        (challenges, s_g, s_h)
    }

    pub fn verify(
        &self,
        gens: BaseGens,
        transcript: &mut merlin::Transcript,
        C: Point,
        c: &[PubScalarZ],
        r: PubScalarNz,
    ) -> bool {
        // Verify that n^2 + l = v for the given commitment.
        let C_i = C.mark::<Jacobian>();
        let mut q = s!(r * r).mark::<Public>();
        // Factors with which we multiply the generators.
        let (challenges, s_g, s_h) =
            self.verification_scalars(transcript, r, gens.G_vec.len(), gens.H_vec.len());

        let lg_n = log(gens.G_vec.len());
        for _ in 0..lg_n {
            q = s!(q * q).mark::<Public>();
        }

        let s_c = Self::s_vec(gens.H_vec.len(), &challenges);
        let l_c = inner_product(&s_c.iter(), &c.iter());

        let v = s!(self.n * self.n * q + self.l * l_c);

        let one = s!(1).mark::<Public>();

        // These collects can be avoided if downstream allows borrow APIs
        let scalar_iter = std::iter::once(one)
            .chain(challenges.iter().copied())
            .chain(
                challenges
                    .iter()
                    .map(|e| s!(e * e - 1).mark::<Public>().mark::<NonZero>().unwrap()),
            )
            .into_iter()
            .collect::<Vec<_>>();

        let point_iter = std::iter::once(C_i)
            .chain(self.x_vec.iter().copied().map(|X| X.mark::<Jacobian>()))
            .chain(self.r_vec.iter().copied().map(|R| R.mark::<Jacobian>()))
            .into_iter()
            .collect::<Vec<_>>();

        let res = secp256kfun::op::lincomb(scalar_iter.iter(), point_iter.iter());

        let g_0 = secp256kfun::op::lincomb(s_g.iter(), gens.G_vec.iter());
        let h_0 = secp256kfun::op::lincomb(s_h.iter(), gens.H_vec.iter());

        let C_0 = g!(v * G + self.n * g_0 + self.l * h_0);
        C_0 == res
    }
}

fn log(n: usize) -> usize {
    32 - 1 - (n as u32).leading_zeros() as usize
}

// Test prove
fn rand_scalar() -> PubScalarZ {
    Scalar::random(&mut thread_rng())
        .mark::<Public>()
        .mark::<Zero>()
}

fn rand_scalar_vec(l: u32) -> Vec<PubScalarZ> {
    (0..l).map(|_| rand_scalar()).collect()
}

fn tester(sz_w: u32, sz_l: u32) {
    let gens = BaseGens::new(sz_w, sz_l);

    let mut transcript = Transcript::new(b"test");

    let mut w = rand_scalar_vec(sz_w);
    let mut l = rand_scalar_vec(sz_l);
    let mut c = rand_scalar_vec(sz_l);
    w[0] = s!(1).mark::<Public>().mark::<Zero>();
    w[1] = s!(3).mark::<Public>().mark::<Zero>();
    w[2] = s!(5).mark::<Public>().mark::<Zero>();
    w[3] = s!(7).mark::<Public>().mark::<Zero>();

    l[0] = Scalar::zero().mark::<Public>();
    c[0] = Scalar::zero().mark::<Public>();

    let r = s!(2).mark::<NonZero>().unwrap().mark::<Public>();
    let q = s!(r * r).mark::<Public>();

    let v = NormProof::v(&w, &l, &c, q);
    let (w_0, l_0, c_0) = (w[0], l[0], c[0]);

    let C = bp_comm(
        v,
        &gens.G_vec.iter(),
        &gens.H_vec.iter(),
        &w.iter(),
        &l.iter(),
    );
    // test norm argument prove
    let prf = NormProof::prove(&mut transcript, gens.clone(), w, l, c.clone(), r);
    dbg!(&prf);

    let mut transcript = Transcript::new(b"test");
    assert!(prf.verify(
        gens,
        &mut transcript,
        C.normalize().mark::<NonZero>().unwrap(),
        &c,
        r,
    ))
}

// fn main() {
//     tester(4, 1);
    // tester(1, 2);
    // tester(1, 4);
    // tester(1, 8);
    // tester(4, 1);
    // tester(8, 1);
    // tester(2, 2);
    // tester(4, 4);
// }
use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

fn bench_prover(ct: &mut Criterion) {
    let sz_w = 64;
    let sz_l = 8;
    let gens = BaseGens::new(sz_w, sz_l);

    let w = rand_scalar_vec(sz_w);
    let l = rand_scalar_vec(sz_l);
    let c = rand_scalar_vec(sz_l);

    // let r = rand_scalar().mark::<NonZero>().unwrap();
    let r = s!(2).mark::<Public>().mark::<NonZero>().unwrap();
    let r = r.invert();
    let q = s!(r*r).mark::<Public>();
    ct.bench_function("prover", |b| {
        b.iter_batched(
            || {
                (
                    gens.clone(),
                    w.clone(),
                    l.clone(),
                    c.clone(),
                    q,
                    Transcript::new(b"test"),
                )
            },
            |(gens, w, l, c, q, mut transcript)| NormProof::prove(&mut transcript, gens, w, l, c, q),
            BatchSize::SmallInput
        )
    });
    let r = rand_scalar().mark::<NonZero>().unwrap();
    let q = s!(r*r).mark::<Public>();
    let v = NormProof::v(&w, &l, &c, q);
    let C = bp_comm(v, &gens.G_vec.iter(), &gens.H_vec.iter(), &w.iter(), &l.iter());
    let C = C.normalize().mark::<NonZero>().unwrap();
    let mut transcript = Transcript::new(b"test");
    // test norm argument prove
    let prf = NormProof::prove(&mut transcript, gens.clone(), w, l, c.clone(), r);

    ct.bench_function("verifier", |b| {
        b.iter_batched(
            || {
                (
                    gens.clone(),
                    c.clone(),
                    Transcript::new(b"test"),
                )
            },
            |(gens, c, mut transcript)| assert!(prf.verify(gens, &mut transcript, C, &c, r)),
            BatchSize::SmallInput
        )
    });
}

// fn criterion_benchmark(c: &mut Criterion) {
//     c.bench_function("tester", |b| b.iter(|| tester(black_box(64), black_box(8))));
// }

criterion_group!(benches, bench_prover);
criterion_main!(benches);
