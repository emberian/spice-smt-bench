//! Reduced exact rationals of Rust's shortest round-trip decimal representation.
//! Decimal digit arithmetic supports the entire finite binary64 range without crates.

fn divide(digits: &mut Vec<u8>, divisor: u8) {
    let mut carry = 0;
    for digit in digits.iter_mut() {
        let n = carry * 10 + *digit;
        *digit = n / divisor;
        carry = n % divisor;
    }
    while digits.len() > 1 && digits[0] == 0 { digits.remove(0); }
}
fn multiply(digits: &mut Vec<u8>, factor: u8) {
    let mut carry = 0;
    for digit in digits.iter_mut().rev() {
        let n = *digit * factor + carry;
        *digit = n % 10;
        carry = n / 10;
    }
    if carry != 0 { digits.insert(0, carry); }
}
fn decimal(digits: Vec<u8>) -> String {
    digits.into_iter().map(|d| char::from(b'0' + d)).collect()
}
/// The exact decimal rational selected by Display, not the binary storage fraction.
/// Distinct finite floats have distinct round-trip decimal representations.
pub fn exact_f64_to_rat(value: f64) -> Result<(bool, String, String), String> {
    if !value.is_finite() { return Err("non-finite numeric constant".into()); }
    if value == 0.0 { return Ok((false, "0".into(), "1".into())); }
    let text = format!("{}", value.abs());
    let (mantissa, exponent) = text.split_once(['e', 'E'])
        .map_or((text.as_str(), 0), |(m, e)| (m, e.parse::<i32>().expect("Display exponent")));
    let places = mantissa.split_once('.').map_or(0, |(_, f)| f.len() as i32);
    let mut digits: Vec<u8> = mantissa.bytes().filter(|c| *c != b'.').map(|c| c-b'0').collect();
    while digits.len() > 1 && digits[0] == 0 { digits.remove(0); }
    let scale = places - exponent;
    if scale <= 0 {
        digits.extend(std::iter::repeat(0).take((-scale) as usize));
        return Ok((value.is_sign_negative(), decimal(digits), "1".into()));
    }
    let mut twos = scale;
    let mut fives = scale;
    while twos > 0 && digits.last().unwrap() % 2 == 0 { divide(&mut digits, 2); twos -= 1; }
    while fives > 0 && digits.last().unwrap() % 5 == 0 { divide(&mut digits, 5); fives -= 1; }
    let mut denominator = vec![1];
    for _ in 0..twos { multiply(&mut denominator, 2); }
    for _ in 0..fives { multiply(&mut denominator, 5); }
    Ok((value.is_sign_negative(), decimal(digits), decimal(denominator)))
}
