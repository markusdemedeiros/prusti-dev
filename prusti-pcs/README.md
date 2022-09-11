# Computation of an interface between Prusti and Rustc 

Run with the feature flag ``dump_operational_pcs`` to compute. 

# Current objective:
- [ ] rewrite the whole thing to clean it up 
    - [ ] finally move to many files!
- [ ] borrow_swap
    - [ ] update tagging 
        - [ ] change to Option Location (None => current) instead of basic blocks
        - [ ] Make sure to never regain tagged permissions (just )
    - [ ] let loan_killed_at regain uninit permissions and tag RHS
- [ ] conditional borrow swap
    - [ ] join will need to properly collect LHS's 

## TODO
- [ ] unsatisfied with meet refactoring
    - [ ] applicative functor api somehow