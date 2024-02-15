use ark_test_curves::{bls12_381, secp256k1, FpConfig};
use num_bigint::{BigUint, RandomBits};
use ark_ec::{AffineRepr, CurveGroup, Group};
use std::{cmp::Ordering, ops::{Add, Mul}};
use ark_std::{rand::Rng, test_rng, UniformRand, Zero};
use ark_ff::{Fp, MontBackend, PrimeField};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

fn main() {
    /* validate the generator
    Public key: 0xaa931f5ee58735270821b3722866d8882d1948909532cf8ac2b3ef144ae8043363d1d3728b49f10c7cd78c38289c8012477473879f3b53169f2a677b7fbed0c7
    Private key: 
    0x227dbb8586117d55284e26620bc76534dfbd2394be34cf4a09cb775d593b6f2b
     */
    // use ark_ff::{BigInteger,BigInteger256};
    // const SK: &str = "227dbb8586117d55284e26620bc76534dfbd2394be34cf4a09cb775d593b6f2b";
    // let sk_hex = hex_string_to_binary_vector(SK);
    // let private_key = BigInteger256::from_bits_be(&sk_hex);
    // let public_key = secp256k1::G1Affine::generator().mul_bigint(private_key);
    // println!("public key: {}", public_key);

    let rng = &mut test_rng();
    // for _ in 0..100  {
    //     let x = rng.sample(RandomBits::new(BIT_X as u64));
    //     prove_equality(x);
    // }

    let zero = BigUint::zero();
    for _ in 0..100  {
        let x: BigUint = rng.sample(RandomBits::new(BIT_X as u64));
        let coin = rng.gen_range(0..100);
        if coin % 2 == 0 {
            prove_or(x.clone(), zero.clone(), x.clone());
        } else {
            prove_or(zero.clone(), x, zero.clone());
        }
    }
}

struct EqualityProof<GP: AffineRepr, GQ: AffineRepr, P: FpConfig<N>, Q: FpConfig<N>, const N: usize> {
    k_p: GP::Group,
    k_q: GQ::Group,
    z: BigUint,
    s_p: Fp<P, N>,
    s_q: Fp<Q, N>,
}

const BIT_C: u32 = 128;
const BIT_X: u32 = 112;
const BIT_F: u32 = 12;

fn pedersen_commit<G: AffineRepr>(
    g: G,
    h: G,
    s: impl AsRef<[u64]>,
    t: impl AsRef<[u64]>,
)  -> G::Group {
    g.mul_bigint(s) + h.mul_bigint(t)
}

fn generate_proof<GP: AffineRepr, GQ: AffineRepr, P: FpConfig<N>, Q: FpConfig<N>, const N: usize>(
    x: BigUint,
    r_p: Fp<P, N>,
    r_q: Fp<Q, N>,
    g_p: GP,
    h_p: GP,
    g_q: GQ,
    h_q: GQ,
    c: BigUint,
) -> EqualityProof<GP, GQ, P, Q, N> {
    let max_x = BigUint::from(2u8).pow(BIT_X);
    assert!(x < max_x);
    let max_c = BigUint::from(2u8).pow(BIT_C);
    assert!(c < max_c);

    let rng = &mut test_rng();

    let k: BigUint = rng.sample(RandomBits::new((BIT_C + BIT_X + BIT_F) as u64));

    let t_p = Fp::<P, N>::rand(rng);
    let t_q = Fp::<Q, N>::rand(rng);

    let k_p = pedersen_commit::<GP>(g_p, h_p, k.clone().to_u64_digits(), t_p.into_bigint());
    let k_q = pedersen_commit::<GQ>(g_q, h_q, k.clone().to_u64_digits(), t_q.into_bigint());

    let c_secp = Fp::<P, N>::from(c.clone());
    let s_p = r_p * c_secp + t_p;
    let c_bls = Fp::<Q, N>::from(c.clone());
    let s_q = r_q * c_bls + t_q;

    let z = c.clone().mul(x) + k.clone();

    let z_low = BigUint::from(2u8).pow(BIT_X + BIT_C);
    let z_high = BigUint::from(2u8).pow(BIT_C + BIT_X + BIT_F) - BigUint::from(1u64);

    assert!(z.cmp(&z_low) > Ordering::Less);
    assert!(z.cmp(&z_high) < Ordering::Greater);

    EqualityProof {
        k_p,
        k_q,
        z,
        s_p,
        s_q,
    }
}

fn prove_equality(
    x: BigUint,
) {
    let rng = &mut test_rng();

    let h_power: BigUint = rng.sample(RandomBits::new(256));
    let secp256_g = secp256k1::G1Affine::generator();
    let secp256_h = secp256_g.mul_bigint(h_power.to_u64_digits()).into_affine();

    let h_power: BigUint = rng.sample(RandomBits::new(256));
    let bls_g = bls12_381::g1::G1Affine::generator();
    let bls_h = bls_g.mul_bigint(h_power.to_u64_digits()).into_affine();

    let r_p = secp256k1::Fr::rand(rng);
    let cm_assets = pedersen_commit::<secp256k1::G1Affine>(
        secp256_g, 
        secp256_h, 
        x.to_u64_digits(), 
        r_p.clone().into_bigint(),
    );

    let r_q = bls12_381::Fr::rand(rng);
    let cm_liability = pedersen_commit::<bls12_381::G1Affine>(
        bls_g, 
        bls_h, 
        x.to_u64_digits(), 
        r_q.clone().into_bigint(),
    );

    let c: BigUint = rng.sample(RandomBits::new(BIT_C as u64));

    let EqualityProof::<secp256k1::G1Affine, bls12_381::G1Affine, MontBackend<secp256k1::FrConfig, 4>, MontBackend<bls12_381::FrConfig, 4>, 4> { 
        k_p, 
        k_q, 
        z, 
        s_p, 
        s_q,
    } = generate_proof(
        x, 
        r_p, 
        r_q, 
        secp256_g, 
        secp256_h, 
        bls_g, 
        bls_h,
        c.clone(),
    );

    let z = z.to_u64_digits();
    let lhs = secp256_g.mul_bigint(z.clone()) + secp256_h.mul_bigint(s_p.into_bigint());
    let rhs = k_p.add(cm_assets.mul_bigint(c.to_u64_digits()));
    println!("eq (1)\nlhs: {}\nrhs: {}", lhs, rhs);
    assert_eq!(lhs, rhs);

    let lhs = bls_g.mul_bigint(z.clone()) + bls_h.mul_bigint(s_q.into_bigint());
    let rhs = k_q.add(cm_liability.mul_bigint(c.to_u64_digits()));
    println!("eq (2)\nlhs: {}\nrhs: {}", lhs, rhs);
    assert_eq!(lhs, rhs);
}

fn hex_string_to_binary_vector(hex_str: &str) -> Vec<bool> {
    use hex::FromHex;
    // Remove the "0x" prefix if present
    let clean_hex_str = if hex_str.starts_with("0x") {
        &hex_str[2..]
    } else {
        hex_str
    };

    // Parse the hexadecimal string into a Vec<u8>
    let hex_bytes = Vec::from_hex(clean_hex_str).expect("Invalid hexadecimal string");

    // Convert bytes to binary vector with true for 1 and false for 0
    hex_bytes
        .iter()
        .flat_map(|&byte| (0..8).rev().map(move |i| (byte >> i) & 1 == 1))
        .collect()
}

fn prove_or (
    x: BigUint,
    target1: BigUint,
    target2: BigUint,
) {
    let rng = &mut test_rng();

    let h_power: BigUint = rng.sample(RandomBits::new(256));
    let secp256_g = secp256k1::G1Affine::generator();
    let secp256_h = secp256_g.mul_bigint(h_power.to_u64_digits()).into_affine();

    let h_power: BigUint = rng.sample(RandomBits::new(256));
    let bls_g = bls12_381::g1::G1Affine::generator();
    let bls_h = bls_g.mul_bigint(h_power.to_u64_digits()).into_affine();

    let r_p = bls12_381::Fr::rand(rng);
    let cm = pedersen_commit::<bls12_381::G1Affine>(
        bls_g, 
        bls_h, 
        x.to_u64_digits(), 
        r_p.clone().into_bigint(),
    );

    let r_q1 = secp256k1::Fr::rand(rng);
    let target1 = pedersen_commit::<secp256k1::G1Affine>(
        secp256_g, 
        secp256_h, 
        target1.to_u64_digits(), 
        r_q1.clone().into_bigint(),
    );

    let r_q2 = secp256k1::Fr::rand(rng);
    let target2 = pedersen_commit::<secp256k1::G1Affine>(
        secp256_g, 
        secp256_h, 
        target2.to_u64_digits(), 
        r_q2.clone().into_bigint(),
    );

    let OrProof::<bls12_381::G1Affine, secp256k1::G1Affine, MontBackend<bls12_381::FrConfig, 4>, MontBackend<secp256k1::FrConfig, 4>, 4> {
        k_p1,
        k_q1,
        k_p2,
        k_q2,
        z1,
        z2,
        s_p1,
        s_q1,
        s_p2,
        s_q2,
        c,
        c1,
        c2,
    } = generate_or_proof::<bls12_381::G1Affine, secp256k1::G1Affine, MontBackend<bls12_381::FrConfig, 4>, MontBackend<secp256k1::FrConfig, 4>, 4>(
        x, 
        r_p, 
        r_q1, 
        r_q2, 
        bls_g, 
        bls_h,
        secp256_g, 
        secp256_h, 
        target1,
    );

    assert_eq!(c, c1.clone()^c2.clone());

    let z = z1.to_u64_digits();
    let lhs = bls_g.mul_bigint(z.clone()) + bls_h.mul_bigint(s_p1.into_bigint());
    let rhs = k_p1.add(cm.mul_bigint(c1.to_u64_digits()));
    println!("eq (1)\nlhs: {}\nrhs: {}", lhs, rhs);
    assert_eq!(lhs, rhs);

    let lhs = secp256_g.mul_bigint(z.clone()) + secp256_h.mul_bigint(s_q1.into_bigint());
    let rhs = k_q1.add(target1.mul_bigint(c1.to_u64_digits()));
    println!("eq (2)\nlhs: {}\nrhs: {}", lhs, rhs);
    assert_eq!(lhs, rhs);

    let z = z2.to_u64_digits();
    let lhs = bls_g.mul_bigint(z.clone()) + bls_h.mul_bigint(s_p2.into_bigint());
    let rhs = k_p2.add(cm.mul_bigint(c2.to_u64_digits()));
    println!("eq (3)\nlhs: {}\nrhs: {}", lhs, rhs);
    assert_eq!(lhs, rhs);

    let lhs = secp256_g.mul_bigint(z.clone()) + secp256_h.mul_bigint(s_q2.into_bigint());
    let rhs = k_q2.add(target2.mul_bigint(c2.to_u64_digits()));
    println!("eq (4)\nlhs: {}\nrhs: {}", lhs, rhs);
    assert_eq!(lhs, rhs);
}

struct OrProof<GP: AffineRepr, GQ: AffineRepr, P: FpConfig<N>, Q: FpConfig<N>, const N: usize> {
    k_p1: GP::Group,
    k_q1: GQ::Group,
    k_p2: GP::Group,
    k_q2: GQ::Group,
    z1: BigUint,
    z2: BigUint,
    s_p1: Fp<P, N>,
    s_q1: Fp<Q, N>,
    s_p2: Fp<P, N>,
    s_q2: Fp<Q, N>,
    c: BigUint,
    c1: BigUint,
    c2: BigUint,
}

// always fake the first proof
fn generate_or_proof<GP: AffineRepr, GQ: AffineRepr, P: FpConfig<N>, Q: FpConfig<N>, const N: usize>(
    x: BigUint,
    r_p: Fp<P, N>,
    r_q1: Fp<Q, N>,
    r_q2: Fp<Q, N>,
    g_p: GP,
    h_p: GP,
    g_q: GQ,
    h_q: GQ,
    target1: GQ::Group,
) -> OrProof<GP, GQ, P, Q, N> {
    let max_x = BigUint::from(2u8).pow(BIT_X);
    assert!(x < max_x);

    let rng = &mut test_rng();

    let c1: BigUint = rng.sample(RandomBits::new(BIT_C as u64));

    let k2: BigUint = rng.sample(RandomBits::new((BIT_C + BIT_X + BIT_F) as u64));
    let t_p2 = Fp::<P, N>::rand(rng);
    let t_q2 = Fp::<Q, N>::rand(rng);
    let k_p2 = pedersen_commit::<GP>(g_p, h_p, k2.clone().to_u64_digits(), t_p2.into_bigint());
    let k_q2 = pedersen_commit::<GQ>(g_q, h_q, k2.clone().to_u64_digits(), t_q2.into_bigint());

    let z1: BigUint = rng.sample(RandomBits::new((BIT_C + BIT_X + BIT_F) as u64));

    let t_p1 = Fp::<P, N>::rand(rng);
    let t_q1 = Fp::<Q, N>::rand(rng);

    let cm = g_p.mul_bigint(x.to_u64_digits());
    let cm = cm.mul_bigint(c1.to_u64_digits());
    let k_p1 = g_p.mul_bigint(z1.to_u64_digits()) - cm;
    let k_p1 = k_p1 + h_p.mul_bigint(t_p1.into_bigint());

    let dl = target1 - h_q.mul_bigint(r_q1.into_bigint());
    let target = dl.mul_bigint(c1.to_u64_digits());
    let k_q1 = g_q.mul_bigint(z1.to_u64_digits()) - target;
    let k_q1 = k_q1 + h_q.mul_bigint(t_q1.into_bigint());

    // only k_p1 and k_p2 for simplicity, better hash k_p1, k_q2, k_p2, k_q2 all together as the challenge
    let c = BigUint::from(calculate_hash(&[&k_p1, &k_p2]));
    let c2 = c.clone()^c1.clone();

    let max_c = BigUint::from(2u8).pow(BIT_C);
    assert!(c2 < max_c);

    let c_p1 = Fp::<P, N>::from(c1.clone());
    let s_p1 = r_p * c_p1 + t_p1;
    let c_q1 = Fp::<Q, N>::from(c1.clone());
    let s_q1 = r_q1 * c_q1 + t_q1;

    let c_p2 = Fp::<P, N>::from(c2.clone());
    let s_p2 = r_p * c_p2 + t_p2;
    let c_q2 = Fp::<Q, N>::from(c2.clone());
    let s_q2 = r_q2 * c_q2 + t_q2;

    let z2 = c2.clone().mul(x.clone()) + k2.clone();

    let z_low = BigUint::from(2u8).pow(BIT_X + BIT_C);
    let z_high = BigUint::from(2u8).pow(BIT_C + BIT_X + BIT_F) - BigUint::from(1u64);

    assert!(z1.cmp(&z_low) > Ordering::Less);
    assert!(z1.cmp(&z_high) < Ordering::Greater);

    assert!(z2.cmp(&z_low) > Ordering::Less);
    assert!(z2.cmp(&z_high) < Ordering::Greater);

    OrProof {
        k_p1,
        k_q1,
        k_p2,
        k_q2,
        z1,
        z2,
        s_p1,
        s_q1,
        s_p2,
        s_q2,
        c,
        c1,
        c2,
    }
}

fn calculate_hash<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}
