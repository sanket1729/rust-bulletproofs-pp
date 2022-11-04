#![allow(non_snake_case)]

/// Rangeproof implementation using norm argument
use crate::norm_arg::{self, NormProof};
use merlin::Transcript;
use norm_arg::BaseGens;
use rand::{CryptoRng, RngCore};
use secp256kfun::{Point, Scalar, g, G, s, marker::{Secret, Zero, Mark, Public, Jacobian, NonZero, Secrecy, ZeroChoice}};

/// Round 1 artifacts
#[derive(Debug, Clone)]
struct Round1Commitments {
    /// Round 1 output: D
    D: Point<Jacobian>,
    /// Round 1 output: M
    M: Point<Jacobian>,
}

#[derive(Debug, Clone)]
struct Round1Secrets {
    /// Vector of digits committed with G_vec
    d: Vec<Scalar<Secret, Zero>>,
    /// Blinding factor for d in G
    b_d: Scalar,
    /// Blinding factor for d in H_vec
    l_d: Vec<Scalar<Secret, Zero>>,
    /// Vector of multiplicities
    m: Vec<Scalar<Secret, Zero>>,
    /// Blinding factor for m in G
    b_m: Scalar,
    /// Blinding factor for m in H_vec
    l_m: Vec<Scalar<Secret, Zero>>,
}

#[derive(Debug, Clone)]
struct Round2Commitments {
    /// Reciprocal commitment: R
    R: Point<Jacobian>,
}

#[derive(Debug, Clone)]
struct Round2Secrets {
    /// Reciprocal vector. This is non-zero, but having zero helps in code-dedup
    r: Vec<Scalar<Secret, Zero>>,
    /// Blinding factor for r in G
    b_r: Scalar,
    /// Blinding factor for r in H_vec
    l_r: Vec<Scalar<Secret, Zero>>,
}

#[derive(Debug, Clone)]
struct Round3Commitments {
    /// Round 3 blinding commitment S
    S: Point<Jacobian, Public, NonZero>,
}

#[derive(Debug, Clone)]
struct Round3Secrets {
    /// Round 3 blinding factor b_s
    b_s: Scalar,
    /// Final w_v(T) polynomial
    w: Poly<Secret>,
    /// Final l_v(T) polynomial
    l: Poly<Secret>,
}

#[derive(Debug, Clone)]
pub struct Prover<'a>{
    /// The base generators
    gens: &'a BaseGens,
    /// `b` base representation of the value to be proven(2, 4, 8, 16)
    base: u64,
    /// `n` number of bits in the value to be proven(32, 64, 128) in base 2
    num_bits: u64,
    /// The commitment to the value
    V: &'a Point,
    /// The value to prove
    v: u64,
    /// The blinding factor. In bulletproofs++, this is actually a vector of 8 values
    /// but as a convention, we set the remaining 7 values to 0.
    gamma: Scalar<Secret, Zero>,
    /// Round 1 commitments
    r1_comm: Option<Round1Commitments>,
    /// Round 1 secrets
    r1_sec: Option<Round1Secrets>,
    /// Round 2 commitments
    r2_comm: Option<Round2Commitments>,
    /// Round 2 secrets
    r2_sec: Option<Round2Secrets>,
    /// Round 3 commitments
    r3_comm: Option<Round3Commitments>,
    /// Round 3 secrets
    r3_sec: Option<Round3Secrets>,
}

#[derive(Debug, Clone)]
pub struct Verifier<'a>{
    /// The base generators
    gens: &'a BaseGens,
    /// `b` base representation of the value to be proven(2, 4, 8, 16)
    base: u64,
    /// `n` number of bits in the value to be proven(32, 64, 128)
    num_bits: u64,
    /// The commitment to the value
    V: &'a Point,
}

#[derive(Debug, Clone)]
pub struct Proof {
    /// Round 1 commitments
    r1_comm: Round1Commitments,
    /// Round 2 commitments
    r2_comm: Round2Commitments,
    /// Round 3 commitments
    r3_comm: Round3Commitments,
    /// w vector
    w: Vec<Scalar<Public, Zero>>,
    /// l vector
    l: Vec<Scalar<Public, Zero>>,
    /// norm proof
    norm_proof: NormProof,
}

// Create a commit C = vG + gamma*H_0
pub fn commit(gens: &BaseGens, v: u64, gamma: &Scalar<Secret, Zero>) -> Point<Jacobian> {
    let mut bytes = [0u8; 32];
    bytes[24..].copy_from_slice(&v.to_be_bytes());
    let v = Scalar::from_bytes(bytes).unwrap();
    let h_0 = gens.H_vec[0];
    g!(v * G + gamma * h_0).mark::<NonZero>().expect("Zero commitment")
}

impl<'a> Prover<'a> {

    pub fn new(gens: &'a BaseGens, base: u64, num_bits: u64, V: &'a Point, v: u64, gamma: Scalar<Secret, Zero>) -> Self {
        assert!(base.is_power_of_two());
        assert!(num_bits.is_power_of_two());
        assert!(num_bits >= crate::log(base as usize) as u64);
        assert!(gens.H_vec.len() == 8);
        Self { gens, base, num_bits, V, v, gamma, r1_comm: None, r1_sec: None, r2_comm: None, r2_sec: None, r3_comm: None, r3_sec: None }
    }

    /// Obtain the number of digits in the base representation
    fn num_digits(&self) -> usize {
        self.num_bits as usize/ crate::log(self.base as usize)
    }

    /// Proving in base n
    fn prove_round_1<R: CryptoRng + RngCore>(&mut self, rng: &mut R) {

        let num_base_bits = crate::log(self.base as usize);
        let num_digits = (self.num_bits as usize) / num_base_bits;
        let mut v1 = self.v;

        let mut d = Vec::with_capacity(num_digits);
        println!("num_digits: {}", num_digits);
        for _ in 0..num_digits {
            d.push(v1 % self.base);
            v1 = v1 >> num_base_bits;
        }

        let mut m = vec![0; self.base as usize];
        for dig in d.iter() {
            m[*dig as usize] += 1u64;
        }

        let d = d.into_iter().map(|x| Scalar::from(x as u32)).collect::<Vec<_>>();
        let m = m.into_iter().map(|x| Scalar::from(x as u32)).collect::<Vec<_>>();

        let mut l_m = std::iter::repeat(Scalar::random(rng).mark::<Zero>()).take(6).collect::<Vec<_>>();
        let mut l_d = std::iter::repeat(Scalar::zero()).take(6).collect::<Vec<_>>();
        l_d[4] = -l_m[5].clone();
        l_d[2] = -l_m[3].clone();
        let (b_d, D) = bp_pp_comm(rng, &self.gens, &d, &l_d);
        let (b_m, M) = bp_pp_comm(rng, &self.gens, &m, &l_m);

        self.r1_sec = Some(Round1Secrets { d, b_d, l_d, m, b_m, l_m });
        self.r1_comm = Some(Round1Commitments { D, M });
    }

    fn prove_round_2<R: CryptoRng + RngCore>(&mut self, rng: &mut R, e: Scalar<Public>) {
        // compute r_i = (1/ (e + d_i))
        let r = self.r1_sec.as_ref().unwrap().d.iter().
            map(|x| s!(e + x).mark::<NonZero>().unwrap().invert().mark::<Zero>()).collect::<Vec<_>>();

        let l_r = std::iter::repeat(Scalar::zero()).take(6).collect::<Vec<_>>();
        let (b_r, R) = bp_pp_comm(rng, &self.gens, &r, &l_r);
        self.r2_sec = Some(Round2Secrets { r, b_r, l_r});
        self.r2_comm = Some(Round2Commitments { R });
    }

    fn prove_round_3<R: CryptoRng + RngCore>(&mut self, rng: &mut R, x: Scalar<Public>, y: Scalar<Public>, q: Scalar<Public>, e: Scalar<Public>) {
        let d = self.r1_sec.as_ref().unwrap().d.clone();
        let m = self.r1_sec.as_ref().unwrap().m.clone();
        let r = self.r2_sec.as_ref().unwrap().r.clone();
        let l_d = self.r1_sec.as_ref().unwrap().l_d.clone();
        let l_m = self.r1_sec.as_ref().unwrap().l_m.clone();
        let l_r = self.r2_sec.as_ref().unwrap().l_r.clone();
        let q_inv_pows = q_inv_pows(q, self.gens.G_vec.len());

        let alpha_r = alpha_r_q_inv_pow(self.num_digits(), x, e, &q_inv_pows);
        let alpha_d = alpha_d_q_inv_pow(self.base, self.num_digits(), &q_inv_pows);
        let alpha_m = alpha_m_q_inv_pows(e, x, self.base as usize, &q_inv_pows);
        let alpha_m = alpha_m.into_iter().map(|x| x.mark::<Secret>()).collect::<Vec<_>>();

        let t_2 = add_vecs(&d, &alpha_r);
        let t_3 = add_vecs(&r, &alpha_d);

        let s = std::iter::repeat(Scalar::random(rng).mark::<Zero>()).take(self.gens.G_vec.len()).collect::<Vec<_>>();
        // let s = std::iter::repeat(Scalar::one().mark::<Zero>()).take(self.gens.G_vec.len()).collect::<Vec<_>>();

        let w_vec = Poly{
            coeffs: vec![s.clone(), m.clone(), t_2, t_3, alpha_m],
        };

        let w_w_q = w_vec.w_q_norm(q);
        dbg!(&w_w_q);
        let zero = Scalar::zero().mark::<Public>();
        let y_inv = y.invert();
        let y = y.mark::<Zero>();
        let c = c_poly(y);
        let two_gamma = s!(2*self.gamma);
        let mut l_vec = Poly {
            coeffs: vec![Vec::new(), l_m, l_d, l_r, Vec::new(), vec![two_gamma], Vec::new(), Vec::new()],
        };
        let l_vec_w_q = l_vec.mul_c(&c);
        dbg!(&l_vec_w_q);
        let mut l_s = Vec::with_capacity(self.gens.H_vec.len());
        for i in 0..self.gens.H_vec.len() {
            let w_w_q_i = &w_w_q[i];
            let l_vec_w_q_i = &l_vec_w_q[i];
            dbg!(i, s!(w_w_q_i + l_vec_w_q_i));
            l_s.push(s!(-w_w_q_i - l_vec_w_q_i));
        }
        let (b_m, b_d, b_r) = (&self.r1_sec.as_ref().unwrap().b_m, &self.r1_sec.as_ref().unwrap().b_d, &self.r2_sec.as_ref().unwrap().b_r);
        let arr = [b_m, b_d, b_r];
        dbg!(&arr);
        for (i, b_i) in arr.into_iter().enumerate() {
            let l_s_i = &l_s[i + 1];
            l_s[i + 1] = s!(l_s_i + b_i);
        }
        {
            // print ls
            for (i, l_s_i) in l_s.iter().enumerate() {
                dbg!(-l_s_i);
            }
        }
        l_s.remove(5);
        l_s.remove(0);
        for l_s_i in l_s.iter_mut() {
            let borrow_ls_i = &*l_s_i;
            *l_s_i = s!( borrow_ls_i * y_inv);
        }
        {
            // print ls
            for (i, l_s_i) in l_s.iter().enumerate() {
                dbg!(i, -l_s_i);
            }
        }
        l_vec.coeffs[0] = l_s.clone();
        // Compute b_s = q^(i+1)s[i]
        let mut q_pow = q.clone();
        let mut b_s = Scalar::zero();
        let s = &w_vec.coeffs[0];
        for i in 0..s.len() {
            let s_i = &s[i];
            b_s = s!(b_s + q_pow * s_i * s_i);
            q_pow = s!(q_pow * q).mark::<Public>();
        }
        // Test assertions
        {
            let w2 = w_vec.w_q_norm(q);
            let l2 = l_vec.mul_c(&c);
            let res = add_vecs(&w2, &l2);

            let v = vec![
                -b_s.clone(), -b_d.clone().mark::<Zero>(), -b_m.clone().mark::<Zero>(), -b_r.clone().mark::<Zero>()
            ];

            let res2 = add_vecs(&res, &v);

            dbg!(&res);
            dbg!(&v);
            dbg!(&res2);
        }
        // Compute S = s*G_vec + l_s*H_vec + b_s*G
        let mut S = g!(b_s * G);
        for (g, w_i) in self.gens.G_vec.iter().zip(s.iter()) {
            S = g!(S + w_i * g);
        }
        for (h, w_i) in self.gens.H_vec.iter().zip(l_s.iter()) {
            S = g!(S + w_i * h);
        }

        // Recompute the secret w
        self.r3_sec = Some(Round3Secrets { b_s: b_s.mark::<NonZero>().unwrap(), w: w_vec, l: l_vec });
        self.r3_comm = Some(Round3Commitments { S: S.mark::<NonZero>().unwrap() });
    }

    fn r1_challenge_e(&self, t: &mut Transcript) -> Scalar<Public> {
        r1_challenge_e(t, self.r1_comm.as_ref().unwrap(), self.num_bits, self.base, self.V)
    }

    fn r2_challenges(&self, t: &mut Transcript) -> (Scalar<Public>, Scalar<Public>, Scalar<Public>, Scalar<Public>) {
        r2_challenges(t, self.r2_comm.as_ref().unwrap())
    }

    fn r3_challenge(&self, t: &mut Transcript) -> Scalar<Public> {
        r3_challenge(t, self.r3_comm.as_ref().unwrap())
    }

    fn proof(self, y: Scalar<Public>, t: Scalar<Public>, r: Scalar<Public>, transcript: &mut Transcript) -> Proof {
        fn print_neg_vec(v: &[Scalar<Public, Zero>]) {
            for (i, v_i) in v.iter().enumerate() {
                println!("{} {} {} {}", i, -v_i, v_i, s!(v_i + v_i));
            }
        }
        let r3_sec = self.r3_sec.unwrap();
        let w_eval = r3_sec.w.eval(t);
        let mut l_eval = r3_sec.l.eval(t);
        l_eval.push(Scalar::zero().mark::<Public>());
        l_eval.push(Scalar::zero().mark::<Public>());
        let t_pows = t_pows(t, self.gens.H_vec.len());

        let (t2, t3, t4, t6, t7) = (t_pows[2], t_pows[3], t_pows[4], t_pows[6], t_pows[7]);
        let c_vec = vec![
            s!(y* t).mark::<Public>().mark::<Zero>(),
            s!(y* t2).mark::<Public>().mark::<Zero>(),
            s!(y* t3).mark::<Public>().mark::<Zero>(),
            s!(y* t4).mark::<Public>().mark::<Zero>(),
            s!(y* t6).mark::<Public>().mark::<Zero>(),
            s!(y* t7).mark::<Public>().mark::<Zero>(),
            Scalar::zero().mark::<Public>(),
            Scalar::zero().mark::<Public>(),
        ];

        let norm_prf = norm_arg::NormProof::prove(
            transcript, self.gens.clone(), w_eval.clone(), l_eval.clone(), c_vec, r
        );
        Proof {
            r1_comm: self.r1_comm.unwrap(),
            r2_comm: self.r2_comm.unwrap(),
            r3_comm: self.r3_comm.unwrap(),
            w: w_eval,
            l: l_eval,
            norm_proof: norm_prf,
        }
    }

    pub fn prove<R: RngCore + CryptoRng>(mut self, rng: &mut R, transcript: &mut Transcript) -> Proof {

        // Round 1
        self.prove_round_1(rng);
        let e = self.r1_challenge_e(transcript);
        dbg!(&self.r1_sec);

        // Round 2
        self.prove_round_2(rng, e);
        let (x, y, r, q) = self.r2_challenges(transcript);
        dbg!(&self.r2_sec);
        {
            let temp = &self.r2_sec.as_ref().unwrap().r[0];
            let res = s!(temp + temp);
        }

        // Round 3
        self.prove_round_3(rng, x, y, q, e);
        let t = self.r3_challenge(transcript);
        dbg!(&self.r3_sec);

        // {
        //     println!("s[0] {}", self.r3_sec.as_ref().unwrap().w.coeffs[0][0]);
        //     println!("m[0] {}", self.r1_sec.as_ref().unwrap().m[0]);
        //     println!("d[0] {}", self.r1_sec.as_ref().unwrap().d[0]);
        //     println!("r[0] {}", self.r2_sec.as_ref().unwrap().r[0]);

        //     println!("s[1] {}", self.r3_sec.as_ref().unwrap().w.coeffs[0][1]);
        //     println!("m[1] {}", self.r1_sec.as_ref().unwrap().m[1]);
        //     println!("d[1] {}", self.r1_sec.as_ref().unwrap().d[1]);
        //     println!("r[1] {}", self.r2_sec.as_ref().unwrap().r[1]);

        //     println!("b_s {}", self.r3_sec.as_ref().unwrap().b_s);
        //     println!("b_d {}", self.r1_sec.as_ref().unwrap().b_d);
        //     println!("b_m {}", self.r1_sec.as_ref().unwrap().b_m);
        //     println!("b_r {}", self.r2_sec.as_ref().unwrap().b_r);

        //     println!("-l_s[0] {}", -&self.r3_sec.as_ref().unwrap().l.coeffs[0][0]);
        //     println!("-l_s[1] {}", -&self.r3_sec.as_ref().unwrap().l.coeffs[0][1]);
        //     println!("-l_s[2] {}", -&self.r3_sec.as_ref().unwrap().l.coeffs[0][2]);
        //     println!("-l_s[3] {}", -&self.r3_sec.as_ref().unwrap().l.coeffs[0][3]);
        //     println!("-l_s[4] {}", -&self.r3_sec.as_ref().unwrap().l.coeffs[0][4]);
        //     println!("-l_s[5] {}", -&self.r3_sec.as_ref().unwrap().l.coeffs[0][5]);

        //     println!("l_d[0] {}", self.r1_sec.as_ref().unwrap().l_d);
        //     println!("l_m[0] {}", self.r1_sec.as_ref().unwrap().l_m);
        //     println!("l_r[0] {}", self.r2_sec.as_ref().unwrap().l_r);
        // }
        // Round 4
        self.proof(y, t, r, transcript)
    }
}

impl<'a> Verifier<'a> {

    pub fn new(gens: &'a BaseGens, base: u64, num_bits: u64, V: &'a Point) -> Self {
        assert!(base.is_power_of_two());
        assert!(num_bits.is_power_of_two());
        assert!(num_bits >= crate::log(base as usize) as u64);
        assert!(gens.H_vec.len() == 8);
        Self { gens, base, num_bits, V }
    }

    /// Obtain the number of digits
    fn num_digits(&self) -> usize {
        (self.num_bits / crate::log(self.base as usize) as u64) as usize
    }

    fn r1_challenge_e(&self, t: &mut Transcript, prf: &Proof) -> Scalar<Public> {
        r1_challenge_e(t, &prf.r1_comm, self.num_bits, self.base, self.V)
    }

    fn r2_challenges(&self, t: &mut Transcript, prf: &Proof) -> (Scalar<Public>, Scalar<Public>, Scalar<Public>, Scalar<Public>) {
        r2_challenges(t, &prf.r2_comm)
    }

    fn r3_challenge(&self, t: &mut Transcript, prf: &Proof) -> Scalar<Public> {
        r3_challenge(t, &prf.r3_comm)
    }

    // The public values to be added to w
    fn g_vec_pub_offsets(&self, e: Scalar<Public>, x: Scalar<Public>, q: Scalar<Public>, t: Scalar<Public>) -> Vec<Scalar<Public, Zero>> {
        let t_pows = t_pows(t, self.gens.H_vec.len());
        let q_inv_pows = q_inv_pows(q, self.gens.G_vec.len());
        let alpha_d = alpha_d_q_inv_pow(self.base, self.num_digits(), &q_inv_pows);
        let alpha_r = alpha_r_q_inv_pow(self.num_digits(), x, e, &q_inv_pows);
        let alpha_m = alpha_m_q_inv_pows(e, x, self.base as usize, &q_inv_pows);

        let alpha_d_t_3 = scalar_mul_vec(&alpha_d, t_pows[3]);
        let alpha_r_t_2 = scalar_mul_vec(&alpha_r, t_pows[2]);
        let alpha_m_t_4 = scalar_mul_vec(&alpha_m, t_pows[4]);

        let res = add_vecs(&alpha_d_t_3, &alpha_r_t_2);
        dbg!(add_vecs(&res, &alpha_m_t_4))
    }

    fn g_offset(&self, e: Scalar<Public>, x: Scalar<Public>, q: Scalar<Public>, t: Scalar<Public>) -> Scalar<Public, Zero> {
        let t_pows = t_pows(t, self.gens.H_vec.len());
        dbg!(&t_pows.len());
        let q_inv_pows = q_inv_pows(q, self.gens.G_vec.len());
        let q_pows = q_pows(q, self.gens.G_vec.len());

        let alpha_d = alpha_d(self.base, self.num_digits());
        let alpha_r2 = alpha_r2(self.num_digits(), e);
        let alpha_d_q_inv_pow = alpha_d_q_inv_pow(self.base, self.num_digits(), &q_inv_pows);
        let alpha_r = alpha_r(self.num_digits(), x);
        let alpha_m_q_inv_pows = alpha_m_q_inv_pows(e, x, self.base as usize, &q_inv_pows);
        let alpha_m = alpha_m(e, x, self.base as usize);

        let t5 = &t_pows[5];
        let t4 = &t_pows[4];
        let two_t_5 = s!(t5 + t5).mark::<Zero>().mark::<Public>();
        let two_t_5_v = vec![two_t_5; self.num_digits()];
        let v_hat_1 = dot(&two_t_5_v, &q_pows);

        let v_hat_2 = dot(&alpha_d, &alpha_r2);
        let v_hat_2 = s!(v_hat_2 * two_t_5).mark::<Zero>().mark::<Public>();

        let v_hat_3 = dot(&alpha_d_q_inv_pow, &alpha_r);
        let v_hat_3 = s!(v_hat_3 * two_t_5).mark::<Zero>().mark::<Public>();

        let v_hat_4 = dot(&alpha_m_q_inv_pows, &alpha_m);
        let v_hat_4 = s!(v_hat_4 * t4 * t4).mark::<Zero>().mark::<Public>();

        dbg!(s!(v_hat_1 + v_hat_2 + v_hat_3));
        dbg!(v_hat_4);
        s!(v_hat_1 + v_hat_2 + v_hat_3 + v_hat_4).mark::<Zero>().mark::<Public>()
    }

    pub fn verify(&self, transcript: &mut Transcript, prf: &Proof) -> bool {
        let e = self.r1_challenge_e(transcript, prf);
        let (x, y, r, q) = self.r2_challenges(transcript, prf);
        let t = self.r3_challenge(transcript, prf);
        let zero = Scalar::zero().mark::<Public>();
        let y = y.mark::<Zero>();
        let t_pows = t_pows(t, self.gens.H_vec.len());

        let (t2, t3, t4, t6, t7) = (t_pows[2], t_pows[3], t_pows[4], t_pows[6], t_pows[7]);
        let c_vec = vec![
            s!(y* t).mark::<Public>(),
            s!(y* t2).mark::<Public>(),
            s!(y* t3).mark::<Public>(),
            s!(y* t4).mark::<Public>(),
            s!(y* t6).mark::<Public>(),
            s!(y* t7).mark::<Public>(),
            Scalar::zero().mark::<Public>(),
            Scalar::zero().mark::<Public>(),
        ];

        let v = norm_arg::NormProof::v(&prf.w, &prf.l, &c_vec, q);
        {
            let (w0, w1, l0, l1, l2, l3, l4, l5) = (
                &prf.w[0],
                &prf.w[1],
                &prf.l[0],
                &prf.l[1],
                &prf.l[2],
                &prf.l[3],
                &prf.l[4],
                &prf.l[5],
            );
            let res = s!(w0*w0 + w1*w1);
            println!("w0*w0 + w1*w1 = {}", res);
            let res2 = s!(l0*t + l1*t2 + l2*t3 + l3*t4 + l4*t6 + l5*t7);
            println!("l0 + l1 + l2 + l3 + l4 + l5 = {}", res2);
            let res3 = s!(res + res2);
            println!("res + res2 = {}", res3);
        }
        dbg!(&v);

        // Compute the commitment to the public values
        let g_offset = self.g_offset(e, x, q, t);
        println!("g_offset: {}", g_offset);
        let ten = Scalar::from(10u32);
        println!("total {}", s!(g_offset + ten));
        let g_vec_pub_offsets = self.g_vec_pub_offsets(e, x, q, t);

        let Proof { r1_comm, r2_comm, r3_comm, w, l, norm_proof } = prf;
        let (S, M, D, R, V) = (&r3_comm.S, &r1_comm.M, &r1_comm.D, &r2_comm.R, self.V);
        let (t2, t3, t5) = (&t_pows[2], &t_pows[3], &t_pows[5]);

        let G_v = secp256kfun::op::lincomb(w.iter(), &self.gens.G_vec);
        let H_v = secp256kfun::op::lincomb(l.iter(), self.gens.H_vec.iter().take(6));

        let C = g!(S + t*M + t2*D + t3*R + t5*V + t5*V);
        // {
        //     // let C = g!(t*M + t2*D + t3*R + t5*V + t5*V);
        //     // let C2 = g!(t5*V + t5*V);
        //     dbg!(&t5);
        //     let ten = Scalar::from(10u32);
        //     let one = Scalar::one();
        //     let (two, six) = (Scalar::from(2u32), Scalar::from(6u32));
        //     let one_half = s!(one + one).mark::<NonZero>().unwrap().invert();
        //     let five = Scalar::from(5u32);
        //     let w1 = &s!(one_half + five);
        //     dbg!(&w1);
        //     let (G0, G1) = (&self.gens.G_vec[0], &self.gens.G_vec[1]);
        //     // assert_eq!(C, g!(w1*G0 + w1*G1 + ten*G + H_v));
        // }
        let P = secp256kfun::op::lincomb(g_vec_pub_offsets.iter(), &self.gens.G_vec);
        let C = g!(C + P + g_offset * G);

        let C1 = g!(G_v + H_v + v * G);
        {
            dbg!(&v);
            dbg!(&w);
            dbg!(&l);
        }
        assert!(C1 == C);
        assert!(norm_proof.verify(self.gens.clone(), transcript, C.normalize().mark::<NonZero>().unwrap(), &c_vec, r));
        C1 == C
    }
}


fn r1_challenge_e(t: &mut merlin::Transcript, r1_comm: &Round1Commitments, n: u64, b: u64, V: &Point) -> Scalar<Public> {
    t.append_message(b"protocol", b"Bulletproofs++");
    t.append_message(b"V", &V.to_bytes());
    t.append_u64(b"n", n);
    t.append_u64(b"b", b);
    t.append_message(b"D", &r1_comm.D.normalize().to_bytes());
    t.append_message(b"M", &r1_comm.M.normalize().to_bytes());
    merlin_scalar(t, b"e")
    // Scalar::one().mark::<Public>()
}

fn r2_challenges(t: &mut merlin::Transcript, r2_comm: &Round2Commitments) -> (Scalar<Public>, Scalar<Public>, Scalar<Public>, Scalar<Public>) {
    t.append_message(b"R", &r2_comm.R.normalize().to_bytes());
    let x = merlin_scalar(t, b"x");
    let y = merlin_scalar(t, b"y");
    let r = merlin_scalar(t, b"r");
    let q = s!(r * r).mark::<Public>();
    (x, y, r, q)
    // let two  = Scalar::from(2u32).mark::<Public>().mark::<NonZero>().unwrap();
    // (Scalar::one().mark::<Public>(), Scalar::one().mark::<Public>(), Scalar::one().mark::<Public>())
}

fn r3_challenge(t: &mut merlin::Transcript, r3_comm: &Round3Commitments) -> Scalar<Public> {
    t.append_message(b"S", &r3_comm.S.normalize().to_bytes());
    merlin_scalar(t, b"t")
    // Scalar::from(3u32).mark::<Public>().mark::<NonZero>().unwrap()
    // Scalar::from(1).mark::<Public>().mark::<NonZero>().unwrap()
}

fn bp_pp_comm<R: CryptoRng + RngCore>(rng: &mut R, gens: &BaseGens, w: &[Scalar<Secret, Zero>], l: &[Scalar<Secret, Zero>]) -> (Scalar, Point<Jacobian>) {
    let b_r = Scalar::random(rng);

    let mut res = g!(b_r * G).mark::<Zero>();
    for (g, w_i) in gens.G_vec.iter().zip(w.iter()) {
        res = g!(res + w_i * g);
    }
    for (h, l_i) in gens.H_vec.iter().zip(l.iter()) {
        res = g!(res + l_i * h);
    }
    (b_r, res.mark::<NonZero>().unwrap())
}

fn merlin_scalar(t: &mut merlin::Transcript, label: &'static [u8]) -> Scalar<Public> {
    let mut bytes = [0u8; 32];
    t.challenge_bytes(label, &mut bytes);
    Scalar::from_bytes(bytes).unwrap().mark::<NonZero>().unwrap().mark::<Public>()
}

// Compute a vector with powers of q (q, q^2, q^3, ...)
fn q_pows(q: Scalar<Public>, n: usize) -> Vec<Scalar<Public>> {
    let mut res = Vec::with_capacity(n as usize);
    let mut q_pow = q;
    for _ in 0..n {
        res.push(q_pow);
        q_pow = s!(q_pow * q).mark::<Public>();
    }
    res
}

// compute powers of t with (1, t, t^2, t^3, ...)
fn t_pows(t: Scalar<Public>, n: usize) -> Vec<Scalar<Public>> {
    let mut res = Vec::with_capacity(n as usize);
    let mut t_pow = Scalar::one().mark::<Public>();
    for _ in 0..n {
        res.push(t_pow);
        t_pow = s!(t_pow * t).mark::<Public>();
    }
    res
}

// Add two vectors of scalars
fn add_vecs<S: Secrecy, S2: Secrecy>(a: &[Scalar<S, Zero>], b: &[Scalar<S2, Zero>]) -> Vec<Scalar<S, Zero>> {
    let (a_len, b_len) = (a.len(), b.len());
    let res_len = std::cmp::max(a_len, b_len);
    let mut res = Vec::with_capacity(res_len);
    let zero_s = Scalar::zero().mark::<S>();
    let zero_pub = Scalar::zero().mark::<S2>();
    for i in 0..res_len {
        let a_i = a.get(i).unwrap_or(&zero_s);
        let b_i = b.get(i).unwrap_or(&zero_pub);
        res.push(s!(a_i + b_i).mark::<S>());
    }
    res
}

// Compute the dot product of two vectors
fn dot<S: Secrecy, Z2: ZeroChoice>(a: &[Scalar<S, Zero>], b: &[Scalar<Public, Z2>]) -> Scalar<S, Zero> {
    let mut res = Scalar::zero().mark::<S>().mark::<Zero>();
    for (a_i, b_i) in a.iter().zip(b.iter()) {
        res = s!(res + a_i * b_i).mark::<S>().mark::<Zero>();
    }
    res
}

// Multiply every element of a vector by a scalar
fn scalar_mul_vec<S: Secrecy, Z: ZeroChoice>(a: &[Scalar<S, Z>], b: Scalar<Public>) -> Vec<Scalar<S, Zero>> {
    let mut res = Vec::with_capacity(a.len());
    for a_i in a.iter() {
        res.push(s!(a_i * b).mark::<S>().mark::<Zero>());
    }
    res
}

// Hadamard product of two vectors of scalars
fn hadamard<S: Secrecy, Z: ZeroChoice>(a: &[Scalar<S, Z>], b: &[Scalar<Public>]) -> Vec<Scalar<S, Zero>> {
    // assert_eq!(a.len(), b.len());
    let mut res = Vec::with_capacity(a.len());
    for (a_i, b_i) in a.iter().zip(b.iter()) {
        res.push(s!(a_i * b_i).mark::<S>().mark::<Zero>());
    }
    res
}

// computes powers of q_inv (q^-1, q^-2, q^-3, ...)
fn q_inv_pows(q: Scalar<Public>, n: usize) -> Vec<Scalar<Public>> {
    let mut res = Vec::with_capacity(n as usize);
    let q_inv = q.invert();
    let mut q_inv_pow = q_inv;
    for _ in 0..n {
        res.push(q_inv_pow);
        q_inv_pow = s!(q_inv_pow * q_inv).mark::<Public>();
    }
    res
}

/// Compute a vector of powers of b (1, b, b^2, b^3, ...) X q_inv_pows
/// Size must be number of digits
fn alpha_d_q_inv_pow(b: u64, n: usize, q_inv_pows: &[Scalar<Public>]) -> Vec<Scalar<Public, Zero>> {
    let res = alpha_d(b, n);
    hadamard(&res, &q_inv_pows)
}

/// Compute a vector of powers of b (1, b, b^2, b^3, ...)
/// Size must be number of digits
fn alpha_d(b: u64, n: usize) -> Vec<Scalar<Public, Zero>> {
    let b = Scalar::from(b as u32).mark::<Public>();
    let mut res = Vec::with_capacity(n as usize);
    let mut b_pow = Scalar::one().mark::<Public>().mark::<Zero>();
    for _ in 0..n {
        res.push(b_pow);
        b_pow = s!(b_pow * b).mark::<Public>();
    }
    res
}

/// Compute alpha_m = vec![1/e, 1/(e + 1), 1/(e + 2), ...] X q_inv_pows
fn alpha_m_q_inv_pows(e: Scalar<Public>, x: Scalar<Public>, n: usize, q_inv_pows: &[Scalar<Public>]) -> Vec<Scalar<Public, Zero>> {
    let res = alpha_m(e, x, n);
    hadamard(&res, q_inv_pows)
}

/// Compute alpha_m = vec![1/e, 1/(e + 1), 1/(e + 2), ...]
fn alpha_m(e: Scalar<Public>, x: Scalar<Public>, n: usize) -> Vec<Scalar<Public, Zero>> {
    let mut res = Vec::with_capacity(n as usize);
    let mut curr_e = e;
    let one = Scalar::one().mark::<Public>();
    for _ in 0..n {
        let curr_e_inv = curr_e.invert();
        res.push(s!(curr_e_inv * x).mark::<Public>().mark::<Zero>());
        curr_e = s!(curr_e + one).mark::<Public>().mark::<NonZero>().unwrap();
    }
    res
}

// Compute a vector of scalar -x
fn alpha_r_q_inv_pow(n: usize, x: Scalar<Public>, e: Scalar<Public>, q_inv_pows: &[Scalar<Public>]) -> Vec<Scalar<Public, Zero>> {
    let res = alpha_r(n, x);
    let alpha_r = hadamard(&res, q_inv_pows);
    add_vecs(&alpha_r, &alpha_r2(n, e))
}

// Compute a vector of scalar -x
fn alpha_r(n: usize, x: Scalar<Public>) -> Vec<Scalar<Public, Zero>> {
    let mut res = Vec::with_capacity(n as usize);
    let minus_one = Scalar::minus_one().mark::<Public>();
    for _ in 0..n {
        res.push(s!(minus_one * x).mark::<Public>().mark::<Zero>());
    }
    res
}

// Compute a vector of [e, e, e, e]
fn alpha_r2(n: usize, e: Scalar<Public>) -> Vec<Scalar<Public, Zero>> {
    std::iter::repeat(e).map(|e| e.mark::<Zero>()).take(n).collect()
}

// obtain the c poly
fn c_poly(y: Scalar<Public, Zero>) -> Poly<Public> {
    let zero = Scalar::zero().mark::<Public>();
    Poly {
        coeffs: vec![vec![zero], vec![y], vec![y], vec![y], vec![y], vec![zero], vec![y], vec![y]],
    }
}

// Obtain the non-zero at i position
fn t_pow_in_c(mut i: usize) -> usize {
    i = i + 1; // i >= 0
    if i >= 5 {
        i = i + 1;
    }
    i
}

#[derive(Debug, Clone)]
struct Poly<S: Secrecy>{
    coeffs: Vec<Vec<Scalar<S, Zero>>>,
}

impl<S: Secrecy> Poly<S> {

    // evaluate the poly at t
    fn eval(&self, t: Scalar<Public>) -> Vec<Scalar<Public, Zero>> {
        let mut res = vec![Scalar::zero().mark::<Public>(); self.coeffs[0].len()];
        let mut t_pow = Scalar::one().mark::<Public>();
        for coeffs in self.coeffs.iter() {
            for (i, coeff) in coeffs.iter().enumerate() {
                let curr = &res[i];
                res[i] = s!(curr + t_pow * coeff).mark::<Secret>().mark::<Zero>().mark::<Public>();
            }
            t_pow = s!(t_pow * t).mark::<Public>();
        }
        res
    }

    // Compute the inner product of two polynomials
    fn w_q_norm(&self, q: Scalar<Public>) -> Vec<Scalar<S, Zero>> {
        let mut res = vec![Scalar::zero().mark::<S>(); 2 * self.coeffs.len() - 1];
        for i in 0..self.coeffs.len() {
            for j in 0..self.coeffs.len() {
                let mut q_pow_i = q;
                let a = &self.coeffs[i];
                let b = &self.coeffs[j];
                let mut inner_prod = Scalar::zero();
                let min_len = a.len().min(b.len());
                for k in 0..min_len {
                    let (a_k, b_k) = (&a[k], &b[k]);
                    inner_prod = s!(inner_prod + a_k * b_k * q_pow_i);
                    q_pow_i = s!(q_pow_i * q).mark::<Public>();
                }
                let res_prev = &res[i + j];
                res[i + j] = s!(res_prev +  inner_prod).mark::<S>();
            }
        }
        res
    }

    // mul c poly
    fn mul_c(&self, c: &Poly<Public>) -> Vec<Scalar<S, Zero>> {
        let mut res = vec![Scalar::zero().mark::<S>(); self.coeffs.len() + c.coeffs.len() - 1];
        for l in 0..self.coeffs.len() {
            let l_vec = &self.coeffs[l];
            for i in 0..l_vec.len() {
                let l_i = &l_vec[i];
                let t_pow_in_c = t_pow_in_c(i);
                if t_pow_in_c >= c.coeffs.len() {
                    continue;
                }
                let c_i = &c.coeffs[t_pow_in_c][0]; // c_vec has exactly one element
                let inner_prod = s!(l_i * c_i);
                let res_prev = &res[l + t_pow_in_c];
                res[l + t_pow_in_c] = s!(res_prev +  inner_prod).mark::<S>();
            }
        }
        res
    }
}

#[cfg(test)]
mod tests{
    use rand::thread_rng;

    use super::*;

    // Test prove and verify
    fn _test_rangeproof(base: u64, num_bits: u64, v: u64) {
        let num_h = 8;
        let num_base_bits = crate::log(base as usize) as u64;
        let num_digits = num_bits / num_base_bits;
        let num_g = std::cmp::max(num_digits, base) as u32;
        let gamma = Scalar::from(3);

        let gens = BaseGens::new(num_g, num_h);
        let V = commit(&gens, v, &gamma).normalize();
        let prover = Prover::new(&gens, base, num_bits, &V, v, gamma);
        let mut transcript = Transcript::new(b"BPP/tests");
        let prf = prover.prove(&mut thread_rng(), &mut transcript);

        let mut transcript = Transcript::new(b"BPP/tests");
        let verifier = Verifier::new(&gens, base, num_bits, &V);
        assert!(verifier.verify(&mut transcript, &prf));
    }

    #[test]
    fn test_rangeproof() {
        for i in 0..16 {
            _test_rangeproof(2, 4, i);
        }
        _test_rangeproof(16, 4, 7);
        _test_rangeproof(16, 8, 243);
        _test_rangeproof(16, 16, 12431);
        _test_rangeproof(16, 32, 134132);
        for _ in 0..100 {
            let v = rand::random::<u64>();
            _test_rangeproof(16, 64, v);
        }
    }

    #[test]
    fn test_inner_prod() {
        let q = Scalar::from(2).mark::<NonZero>().unwrap().mark::<Public>();
        let a = Poly {
            coeffs: vec![
                vec![Scalar::from(1), Scalar::from(2)],
                vec![Scalar::from(1), Scalar::from(2)],
            ]
        };
        let b = Poly {
            coeffs: vec![
                vec![Scalar::from(3), Scalar::from(4)],
                vec![Scalar::from(3), Scalar::from(4)],
            ]
        };
        let res = a.w_q_norm(q);
        assert_eq!(res, vec![Scalar::from(18), Scalar::from(36), Scalar::from(18)]);
    }
}