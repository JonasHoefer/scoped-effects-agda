# Scoped Effects in Agda 

This repository contains an implementation of scoped algebraic effects and handlers in Agda.
The implementation is based on work by [Piróg et al.][paper/PSWJ18] and [Fu and Selinger][paper/FuSelinger18].

The library was developed as part of a [bachelor's thesis][thesis/Hoefer2020] which can be found in the `thesis` directory.

## Structure

The implementation in `src` utilizes scoped algebras, as described by [Wu et al.][paper/PSWJ18], that are implemented using a version of higher order folds, as described by [Fu and Selinger][paper/FuSelinger18].

The `old` directory contains an implementation using explicit scope delimiters and some ultimately failed attempts using higher order functors.
These two implementations closely follow ["Effect Handlers in Scope"][paper/WuSH14].
They are kept for historical and documentation purposes.

## Example

The library implements so called _scoped_ algebraic effects.
These effects can implement operations which create local scopes, for example `catch` and `local`.
Furthermore, the library contains an implementation of a sharing effect for nondeterminism.
The implementation is based on work by [Bunkenburg][thesis/Bunkenburg19].
This effect allows simulating [Curry's][Software/Curry] call-time choice semantics. 

```agda
coin : ⦃ Nondet ∈ effs ⦄ → Prog effs ℕ
coin = pure 0 ⁇ pure 1

doubleSharedCoin : ⦃ Nondet ∈ effs ⦄ → ⦃ State SID ∈ effs ⦄ → ⦃ Share ∈ effs ⦄ → Prog effs ℕ
doubleSharedCoin = do
  c ← share coin
  ⦇ c + c ⦈
  
_ : runCTC doubleSharedCoin ≡ 0 ∷ 2 ∷ []
_ = refl
```

## Versions
- [Agda][software/agda], versions 2.6.1
- [Agda Standard Library][software/agda-stdlib], version 1.4

## Bibliography

- [Effect Handlers in Scope][paper/WuSH14]
- [Modeling Call Time Choice as Effect using Scoped Free Monads][thesis/Bunkenburg19]
- [Syntax and Semantics for Operations with Scopes][paper/PSWJ18]
- [Dependently Typed Folds for Nested Data Types][paper/FuSelinger18]

[paper/WuSH14]:
  http://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf
  "Effect Handlers in Scope"
  
[thesis/Bunkenburg19]:
  https://bunkenburg.net/papers/ModelingCallTimeChoiceAsEffect.pdf
  "Modeling Call-Time Choice as Effect using Scoped Free Monads"

[paper/PSWJ18]:
  https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/lics2018.pdf
  "Syntax and Semantics for Operations with Scopes"

[paper/FuSelinger18]:
  https://arxiv.org/pdf/1806.05230.pdf
  "Dependently Typed Folds for Nested Data Types"
  
[thesis/Hoefer2020]:
  https://github.com/JonasHoefer/scoped-effects-agda/blob/main/thesis/latex/thesis.pdf
  "Implementing a Library for Scoped Algebraic Effects in Agda"

[software/agda]:
  https://wiki.portal.chalmers.se/agda/Main/Download
  "The Agda Wiki — Downloads"

[software/agda-stdlib]:
  https://wiki.portal.chalmers.se/agda/Libraries/StandardLibrary
  "The Agda Wiki — Standard Library"
  
[software/Curry]:
  http://www.curry-lang.org/
  "Curry Programming Language"
