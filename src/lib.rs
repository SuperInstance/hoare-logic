//! # hoare-logic
//!
//! Hoare logic with weakest precondition, strongest postcondition, and
//! verification condition generation.
//!
//! ## Features
//!
//! - Arithmetic and Boolean assertion language
//! - Hoare triple representation and validity checking
//! - Weakest precondition (WP) computation
//! - Strongest postcondition (SP) computation
//! - Verification condition generation (VCGen) for straight-line programs
//!
//! ## Example
//!
//! ```
//! use hoare_logic::{Assert, Stmt, vcgen};
//!
//! // {x > 0} x := x + 1 {x > 1}
//! let post = Assert::gt_expr("x", 0);
//! let stmt = Stmt::assign("x", "x + 1");
//!
//! let vcs = vcgen(&stmt, &post);
//! println!("VCs: {:?}", vcs);
//! ```

mod assertion;
mod triple;
mod wp;
mod sp;
mod vcgen;

pub use assertion::{Assert, BinExpr, Expr};
pub use triple::{HoareTriple, TripleResult};
pub use wp::weakest_precondition;
pub use sp::strongest_postcondition;
pub use vcgen::{vcgen, Stmt};
