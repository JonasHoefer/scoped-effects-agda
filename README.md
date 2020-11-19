# Scoped Effects in Agda 
![CI Pipeline](https://github.com/JonasHoefer/scoped-effects-agda/workflows/CI%20Pipeline/badge.svg)

Implementations of scoped algebraic effects and handlers in Agda.
The implementation in `src` utilizes scoped algebras as described by [Wu et al.][paper/PSWJ18] implemented using a version of higher order folds as described by [Fu and Selinger][paper/FuSelinger18].

The `old` directory contains an implementation using explicit scope delimiters and some ultimatly failed attempts using higher order functors.
These two implementations closely follow ["Effect Handlers in Scope"][paper/WuSH14].
They are kept for historical/documentation purposes.

Versions
- [Agda][software/agda], versions 2.6.1
- [Agda Standard Library][software/agda-stdlib], version 1.4


## Bibliography

- [Effect Handlers in Scope][paper/WuSH14]
- [Modeling Call Time Choice as Effect using Scoped Free Monads][thesis/Bunkenburg19]
- [Syntax and Semantics for Operations with Scopes][paper/PSWJ18]
- [Dependently Typed Folds for Nested Data Types][paper/FuSelinger18]

[paper/WuSH14]:
  http://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf
  "Effect Handlers in Scope "
  
[thesis/Bunkenburg19]:
  https://bunkenburg.net/papers/ModelingCallTimeChoiceAsEffect.pdf
  "Modeling Call-Time Choice as Effect using Scoped Free Monads"

[paper/PSWJ18]:
  https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/lics2018.pdf
  "Syntax and Semantics for Operations with Scopes"

[paper/FuSelinger18]:
  https://arxiv.org/pdf/1806.05230.pdf
  "Dependently Typed Folds for Nested Data Types"

[software/agda]:
  https://wiki.portal.chalmers.se/agda/Main/Download
  "The Agda Wiki — Downloads"

[software/agda-stdlib]:
  https://wiki.portal.chalmers.se/agda/Libraries/StandardLibrary
  "The Agda Wiki — Standard Library"
