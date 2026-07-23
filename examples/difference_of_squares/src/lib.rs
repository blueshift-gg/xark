
use xark::prelude::*;

#[circuit]
pub fn difference_of_squares(x: Private<Field>, y: Private<Field>, z: Public<Field>) {
    require_eq((x + y) * (x - y), z);
}

#[cfg(test)]
mod tests {
    use super::difference_of_squares;

    #[test]
    fn accepts_valid() {
        // (5+3)·(5−3) = 8·2 = 16
        difference_of_squares("5".into(), "3".into(), "16".into()).unwrap();
    }

    #[test]
    fn rejects_wrong() {
        assert!(difference_of_squares("5".into(), "3".into(), "17".into()).is_err());
    }
}
