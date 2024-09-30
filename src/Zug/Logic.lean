/-- Need some notion of `eventually` -/
inductive Term : Type
| always : Term → Term
| eventually : Term → Term
