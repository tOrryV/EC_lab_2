use num_bigint::{BigInt, BigUint, RandBigInt, ToBigInt};
use num_traits::{One, Zero};
use rand::thread_rng;
use sha2::{Digest, Sha256};
use aes_gcm::{
    aead::{Aead, KeyInit},
    Aes256Gcm, Nonce,
};
use rand::RngCore;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Point {
    Infinity,
    Affine { x: BigUint, y: BigUint },
}

#[derive(Clone, Debug)]
struct Curve {
    p: BigUint,
    a: BigUint,
    b: BigUint,
    g: Point,
    n: BigUint,
}

#[derive(Clone, Debug)]
struct Ciphertext {
    ephemeral_public: Point,
    nonce: [u8; 12],
    data: Vec<u8>,
}

fn hex_biguint(s: &str) -> BigUint {
    BigUint::parse_bytes(s.as_bytes(), 16).expect("invalid hex")
}

fn biguint_to_hex(x: &BigUint) -> String {
    format!("{:x}", x)
}

fn point_to_uncompressed_hex(point: &Point, coord_len: usize) -> String {
    match point {
        Point::Infinity => "INF".to_string(),
        Point::Affine { x, y } => {
            let mut out = String::from("04");
            for b in to_fixed_be_bytes(x, coord_len) {
                out.push_str(&format!("{:02x}", b));
            }
            for b in to_fixed_be_bytes(y, coord_len) {
                out.push_str(&format!("{:02x}", b));
            }
            out
        }
    }
}

fn to_fixed_be_bytes(x: &BigUint, len: usize) -> Vec<u8> {
    let bytes = x.to_bytes_be();
    if bytes.len() >= len {
        return bytes;
    }

    let mut out = vec![0u8; len - bytes.len()];
    out.extend(bytes);
    out
}

fn mod_add(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint {
    (a + b) % m
}

fn mod_sub(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint {
    if a >= b {
        (a - b) % m
    } else {
        (m - ((b - a) % m)) % m
    }
}

fn mod_mul(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint {
    (a * b) % m
}

fn mod_inv(a: &BigUint, m: &BigUint) -> Option<BigUint> {
    if a.is_zero() {
        return None;
    }

    let mut t = BigInt::zero();
    let mut new_t = BigInt::one();
    let mut r = m.to_bigint()?;
    let mut new_r = a.to_bigint()?;

    while new_r != BigInt::zero() {
        let q = &r / &new_r;

        let temp_t = t - &q * &new_t;
        t = new_t;
        new_t = temp_t;

        let temp_r = r - &q * &new_r;
        r = new_r;
        new_r = temp_r;
    }

    if r != BigInt::one() {
        return None;
    }

    let m_big = m.to_bigint()?;
    let mut t = t % &m_big;
    if t < BigInt::zero() {
        t += &m_big;
    }

    t.try_into().ok()
}

impl Curve {
    fn p192() -> Self {
        let p = hex_biguint("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFF");
        let a = hex_biguint("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFFFFFFFFFFFC");
        let b = hex_biguint("64210519E59C80E70FA7E9AB72243049FEB8DEECC146B9B1");
        let gx = hex_biguint("188DA80EB03090F67CBF20EB43A18800F4FF0AFD82FF1012");
        let gy = hex_biguint("07192B95FFC8DA78631011ED6B24CDD573F977A11E794811");
        let n = hex_biguint("FFFFFFFFFFFFFFFFFFFFFFFF99DEF836146BC9B1B4D22831");

        Self {
            p,
            a,
            b,
            g: Point::Affine { x: gx, y: gy },
            n,
        }
    }

    fn is_on_curve(&self, point: &Point) -> bool {
        match point {
            Point::Infinity => true,
            Point::Affine { x, y } => {
                let lhs = mod_mul(y, y, &self.p);
                let x2 = mod_mul(x, x, &self.p);
                let x3 = mod_mul(&x2, x, &self.p);
                let ax = mod_mul(&self.a, x, &self.p);
                let rhs = mod_add(&mod_add(&x3, &ax, &self.p), &self.b, &self.p);
                lhs == rhs
            }
        }
    }

    fn add(&self, p1: &Point, p2: &Point) -> Point {
        match (p1, p2) {
            (Point::Infinity, _) => p2.clone(),
            (_, Point::Infinity) => p1.clone(),
            (
                Point::Affine { x: x1, y: y1 },
                Point::Affine { x: x2, y: y2 },
            ) => {
                if x1 == x2 && ((y1 + y2) % &self.p).is_zero() {
                    return Point::Infinity;
                }

                let lambda = if x1 == x2 && y1 == y2 {
                    if y1.is_zero() {
                        return Point::Infinity;
                    }

                    let three = BigUint::from(3u32);
                    let two = BigUint::from(2u32);

                    let x1_sq = mod_mul(x1, x1, &self.p);
                    let numerator =
                        mod_add(&mod_mul(&three, &x1_sq, &self.p), &self.a, &self.p);
                    let denominator = mod_mul(&two, y1, &self.p);

                    match mod_inv(&denominator, &self.p) {
                        Some(inv) => mod_mul(&numerator, &inv, &self.p),
                        None => return Point::Infinity,
                    }
                } else {
                    let numerator = mod_sub(y2, y1, &self.p);
                    let denominator = mod_sub(x2, x1, &self.p);

                    match mod_inv(&denominator, &self.p) {
                        Some(inv) => mod_mul(&numerator, &inv, &self.p),
                        None => return Point::Infinity,
                    }
                };

                let x3 = mod_sub(
                    &mod_sub(&mod_mul(&lambda, &lambda, &self.p), x1, &self.p),
                    x2,
                    &self.p,
                );
                let y3 = mod_sub(
                    &mod_mul(&lambda, &mod_sub(x1, &x3, &self.p), &self.p),
                    y1,
                    &self.p,
                );

                Point::Affine { x: x3, y: y3 }
            }
        }
    }

    fn scalar_mul(&self, k: &BigUint, point: &Point) -> Point {
        let mut result = Point::Infinity;
        let mut addend = point.clone();
        let mut scalar = k.clone();

        while !scalar.is_zero() {
            if (&scalar & BigUint::one()) == BigUint::one() {
                result = self.add(&result, &addend);
            }
            addend = self.add(&addend, &addend);
            scalar >>= 1usize;
        }

        result
    }

    fn random_scalar_below_n(&self) -> BigUint {
        let mut rng = thread_rng();
        loop {
            let value = rng.gen_biguint_below(&self.n);
            if !value.is_zero() {
                return value;
            }
        }
    }

    fn hash_to_int(&self, message: &[u8]) -> BigUint {
        let digest = Sha256::digest(message);
        let mut e = BigUint::from_bytes_be(&digest);
        let out_bits = digest.len() * 8;
        let n_bits = self.n.bits() as usize;

        if out_bits > n_bits {
            e >>= out_bits - n_bits;
        }

        e
    }

    fn ecdh_shared_point(&self, private_key: &BigUint, public_key: &Point) -> Point {
        self.scalar_mul(private_key, public_key)
    }

    fn ecdsa_sign(&self, private_key: &BigUint, message: &[u8]) -> (BigUint, BigUint) {
        let z = self.hash_to_int(message);

        loop {
            let k = self.random_scalar_below_n();
            let r_point = self.scalar_mul(&k, &self.g);

            let r = match r_point {
                Point::Infinity => continue,
                Point::Affine { x, .. } => x % &self.n,
            };

            if r.is_zero() {
                continue;
            }

            let Some(k_inv) = mod_inv(&k, &self.n) else {
                continue;
            };

            let rd = mod_mul(&r, private_key, &self.n);
            let sum = mod_add(&z, &rd, &self.n);
            let s = mod_mul(&k_inv, &sum, &self.n);

            if s.is_zero() {
                continue;
            }

            return (r, s);
        }
    }

    fn ecdsa_verify(&self, public_key: &Point, message: &[u8], signature: &(BigUint, BigUint)) -> bool {
        let (r, s) = signature;

        if r.is_zero() || s.is_zero() || r >= &self.n || s >= &self.n {
            return false;
        }

        let z = self.hash_to_int(message);
        let Some(w) = mod_inv(s, &self.n) else {
            return false;
        };

        let u1 = mod_mul(&z, &w, &self.n);
        let u2 = mod_mul(r, &w, &self.n);

        let p1 = self.scalar_mul(&u1, &self.g);
        let p2 = self.scalar_mul(&u2, public_key);
        let x_point = self.add(&p1, &p2);

        match x_point {
            Point::Infinity => false,
            Point::Affine { x, .. } => (x % &self.n) == *r,
        }
    }

    /*fn encrypt(&self, recipient_public: &Point, plaintext: &[u8]) -> Ciphertext {
        let k = self.random_scalar_below_n();

        let ephemeral_public = self.scalar_mul(&k, &self.g);
        let shared = self.scalar_mul(&k, recipient_public);

        let shared_x = match &shared {
            Point::Infinity => panic!("unexpected point at infinity in encryption"),
            Point::Affine { x, .. } => x.clone(),
        };

        let keystream = derive_keystream(&shared_x, plaintext.len(), 24);
        let data = xor_bytes(plaintext, &keystream);

        Ciphertext {
            ephemeral_public,
            data,
        }
    }*/

    fn encrypt(&self, recipient_public: &Point, plaintext: &[u8]) -> Ciphertext {
        let k = self.random_scalar_below_n();

        let ephemeral_public = self.scalar_mul(&k, &self.g);
        let shared = self.scalar_mul(&k, recipient_public);

        let shared_x = match &shared {
            Point::Infinity => panic!("unexpected point at infinity in encryption"),
            Point::Affine { x, .. } => x.clone(),
        };

        let key = derive_aes256_key(&shared_x, 24);
        let cipher = Aes256Gcm::new_from_slice(&key).expect("invalid AES key");

        let mut nonce = [0u8; 12];
        thread_rng().fill_bytes(&mut nonce);

        let data = cipher
            .encrypt(Nonce::from_slice(&nonce), plaintext)
            .expect("AES-GCM encryption failed");

        Ciphertext {
            ephemeral_public,
            nonce,
            data,
        }
    }

    /*fn decrypt(&self, recipient_private: &BigUint, ciphertext: &Ciphertext) -> Vec<u8> {
        let shared = self.scalar_mul(recipient_private, &ciphertext.ephemeral_public);

        let shared_x = match shared {
            Point::Infinity => panic!("unexpected point at infinity in decryption"),
            Point::Affine { x, .. } => x,
        };

        let keystream = derive_keystream(&shared_x, ciphertext.data.len(), 24);
        xor_bytes(&ciphertext.data, &keystream)
    }*/

    fn decrypt(&self, recipient_private: &BigUint, ciphertext: &Ciphertext) -> Option<Vec<u8>> {
        let shared = self.scalar_mul(recipient_private, &ciphertext.ephemeral_public);

        let shared_x = match shared {
            Point::Infinity => return None,
            Point::Affine { x, .. } => x,
        };

        let key = derive_aes256_key(&shared_x, 24);
        let cipher = Aes256Gcm::new_from_slice(&key).ok()?;

        cipher
            .decrypt(Nonce::from_slice(&ciphertext.nonce), ciphertext.data.as_ref())
            .ok()
    }
}

/*fn derive_keystream(shared_x: &BigUint, length: usize, field_len: usize) -> Vec<u8> {
    let shared_bytes = to_fixed_be_bytes(shared_x, field_len);
    let mut stream = Vec::with_capacity(length);
    let mut counter: u32 = 0;

    while stream.len() < length {
        let mut hasher = Sha256::new();
        hasher.update(&shared_bytes);
        hasher.update(counter.to_be_bytes());

        let block = hasher.finalize();
        stream.extend_from_slice(&block);

        counter = counter.wrapping_add(1);
    }

    stream.truncate(length);
    stream
}*/

/*fn xor_bytes(data: &[u8], key: &[u8]) -> Vec<u8> {
    data.iter()
        .zip(key.iter())
        .map(|(a, b)| a ^ b)
        .collect()
}*/

fn derive_aes256_key(shared_x: &BigUint, field_len: usize) -> [u8; 32] {
    let shared_bytes = to_fixed_be_bytes(shared_x, field_len);
    let digest = Sha256::digest(&shared_bytes);

    let mut key = [0u8; 32];
    key.copy_from_slice(&digest);
    key
}

fn main() {
    let curve = Curve::p192();
    let coord_len = 24usize;

    println!("=== Eliptic curves parameters: NIST P-192 ===");
    println!("p = {}", biguint_to_hex(&curve.p));
    println!("a = {}", biguint_to_hex(&curve.a));
    println!("b = {}", biguint_to_hex(&curve.b));
    println!("n = {}", biguint_to_hex(&curve.n));
    println!(
        "G = {}",
        point_to_uncompressed_hex(&curve.g, coord_len)
    );
    println!();

    assert!(curve.is_on_curve(&curve.g));
    assert_eq!(curve.scalar_mul(&curve.n, &curve.g), Point::Infinity);

    println!("=== 1. ECDH: agreement of shared secret ===");
    let da = curve.random_scalar_below_n();
    let db = curve.random_scalar_below_n();

    let qa = curve.scalar_mul(&da, &curve.g);
    let qb = curve.scalar_mul(&db, &curve.g);

    let sa = curve.ecdh_shared_point(&da, &qb);
    let sb = curve.ecdh_shared_point(&db, &qa);

    println!("d_A = {}", biguint_to_hex(&da));
    println!("Q_A = {}", point_to_uncompressed_hex(&qa, coord_len));
    println!("d_B = {}", biguint_to_hex(&db));
    println!("Q_B = {}", point_to_uncompressed_hex(&qb, coord_len));

    println!(
        "Shared secret Alice = {}",
        point_to_uncompressed_hex(&sa, coord_len)
    );
    println!(
        "Shared secret Bob   = {}",
        point_to_uncompressed_hex(&sb, coord_len)
    );
    println!("Shared secrets are equal: {}", sa == sb);
    println!();

    println!("=== 2. Encrypted messaging using ephemeral ECDH ===");
    let message = b"Wake up, Neo... The Matrix has you... Follow the white rabbit. Knock, knock, Neo".as_ref();
    /*let ciphertext = curve.encrypt(&qb, message);
    let decrypted = curve.decrypt(&db, &ciphertext);

    println!("Message        : {}", String::from_utf8_lossy(message));
    println!(
        "Ephemeral public key R: {}",
        point_to_uncompressed_hex(&ciphertext.ephemeral_public, coord_len)
    );
    println!("Ciphertext (hex)     : {}", hex::encode(&ciphertext.data));
    println!("Decrypted          : {}", String::from_utf8_lossy(&decrypted));
    println!("Correctness        : {}", decrypted == message);
    println!();*/

    let ciphertext = curve.encrypt(&qb, message);
    let decrypted = curve.decrypt(&db, &ciphertext);

    println!("Message        : {}", String::from_utf8_lossy(message));
    println!(
        "Ephemeral public key R: {}",
        point_to_uncompressed_hex(&ciphertext.ephemeral_public, coord_len)
    );
    println!("Nonce (hex)         : {}", hex::encode(ciphertext.nonce));
    println!("Ciphertext (hex)     : {}", hex::encode(&ciphertext.data));

    match decrypted {
        Some(pt) => {
            println!("Decrypted          : {}", String::from_utf8_lossy(&pt));
            println!("Correctness        : {}", pt == message);
        }
        None => {
            println!("Decryption failed");
        }
    }
    println!();

    println!("=== 3. ECDSA: signature and verification ===");
    let signing_message = b"ECDSA test message on NIST P-192";
    let signature = curve.ecdsa_sign(&da, signing_message);
    let ok = curve.ecdsa_verify(&qa, signing_message, &signature);
    let tampered_ok = curve.ecdsa_verify(&qa, b"tampered", &signature);

    println!(
        "Message        : {}",
        String::from_utf8_lossy(signing_message)
    );
    println!("r = {}", biguint_to_hex(&signature.0));
    println!("s = {}", biguint_to_hex(&signature.1));
    println!("Signature is valid    : {}", ok);
    println!("For tampered message: {}", tampered_ok);
}
