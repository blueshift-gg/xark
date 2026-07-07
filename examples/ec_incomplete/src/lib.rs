//! Validate 3-limb incomplete EC ops: 2·G==2G and G+2G==3G (exercises the whole
//! 3×86-bit field stack: add, sub, mul, inverse). Takes aggregate `Point` inputs
//! directly — each `Private<Point>`/`Public<Point>` flattens to 6 `Field` inputs.
#![no_std]
use xark::{assert_eq, Private, Public};
use xark_secp256k1::{ec_add_incomplete, ec_double_incomplete, Point};
fn ceq(got: Point, want: Point) {
    let mut i=0; while i<3 { assert_eq(got.x.limbs[i], want.x.limbs[i]); i+=1; }
    let mut i=0; while i<3 { assert_eq(got.y.limbs[i], want.y.limbs[i]); i+=1; }
}
pub fn circuit(g: Private<Point>, two_g: Public<Point>, three_g: Public<Point>) {
    ceq(ec_double_incomplete(g), two_g);
    ceq(ec_add_incomplete(g, two_g), three_g);
}
