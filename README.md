# hoare-logic

Hoare logic with weakest precondition, strongest postcondition, and verification condition generation.

## Features

- **Assertion language**: Arithmetic expressions, comparisons, logical connectives, quantifiers
- **Weakest precondition (WP)**: Compute WP for assignments, conditionals, sequences, and loops
- **Strongest postcondition (SP)**: Compute SP for straight-line programs
- **Verification condition generation (VCGen)**: Generate VCs for Hoare triples
- **Hoare triples**: Represent and verify `{P} S {Q}` triples

## Installation

```toml
[dependencies]
hoare-logic = "0.1.0"
```

## Usage

```rust
use hoare_logic::{Assert, Expr, Stmt, vcgen, weakest_precondition};

// {true} x := 5 {x > 0}
let post = Assert::gt(Expr::var("x"), 0);
let stmt = Stmt::assign("x", "5");
let vcs = vcgen(&stmt, &post);
// VC: 5 > 0 (which is trivially true)

// While loop with invariant
let stmt = Stmt::while_with_inv(
    "x > 0",
    "x >= 0",
    Stmt::assign("x", "x - 1"),
);
let vcs = vcgen(&stmt, &post);
```

## Architecture

| Module | Description |
|--------|-------------|
| `assertion` | Expression and assertion language |
| `triple` | Hoare triple and statement definitions |
| `wp` | Weakest precondition computation with expression parser |
| `sp` | Strongest postcondition computation |
| `vcgen` | Verification condition generation |

## License

MIT OR Apache-2.0
