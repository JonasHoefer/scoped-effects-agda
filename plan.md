# Implementing a library for scoped algebraic effects in Agda

Algebraische Effekte und deren Handler werden in der funktionalen Community immer beliebter: insbesondere in Haskell [1,2,3,4, 5] und Scala [6,7,8] gibt es neben zahlreichen Implementierungen von Effekt-Bibliotheken auch eine Vielzahl von Anwendungen, die auf die Trennung von Syntax und Semantik, die algebraischen Effekten zugrunde liegt, setzen.
In Sprachen wie Idris, Agda und Coq fallen die Suchergebnisse schon knapper aus; insbesondere fuer Agda findet man nur eine Reimplementierung auf Basis von Idris [9, 10].
Im Rahmen dieser Bachelorarbeit soll eine Effekt-Bibliothek fuer Agda implementiert werden, die insbesondere sogenannte _scoped effects_ [11] unterstuetzt.
So basiert z.B. die Haskell-Bibliothek fused-effects auf den Grundideen dieser wissenschaftlichen Arbeit.
Der Vorteil bei der Verwendung der Sprache Agda liegt dabei in einer zusaetzlichen Sicherheit bei der Implementierung: die Konstruktionen, die bei algebraischen Effekten zur Verfuegung gestellt werden, folgen gewissen (algebraischen) Gesetzen.
Mit der Implementierung so einer Bibliothek ist also der Grundstein gelegt, um die Implementierung bzgl. dieser Gesetze zu verifizieren.

Die Arbeit "Effect Handlers in Scope" stellt dabei zwei verschiedene Ansaetze zur Unterstuetzung von _scoped effects_ vor, die wir im folgenden durch _first order_ und _higher-order_ unterscheiden.

# Plan

* Einarbeitung in "Effect Handlers in Scope" [11] (0,5 Wochen)

* Portierung der Implementierung (first order) in Agda auf Basis der aktuellen Kenntnisse zur Modellierung von freien Monaden mithilfe von container-Darstellung von Funktoren (1 Woche)
* Reimplementierung und Testen einfacher Beispielprogramme ohne _scoped effects_ (0,5 Wochen)
* Reimplementierung und Testen der Beispiele fuer _scoped effects_ (1 Woche)
* Testen der Implementierung (first order) anhand von call-time choice als _scoped effect_ [12] (1 Woche)
* Aufschrieb fuer diesen Teil (1 Woche)

--------
5 Wochen

* Portierung der Implementierung (higher-order) in Agda auf Basis der aktuellen Kenntnisse zur Modellierung von freien Monaden mithilfe von container-Darstellung von Funktoren (2 Wochen)
* Reimplementierung und Testen einfacher Beispielprogramme ohne _scoped effects_ (0,5 Wochen)
* Reimplementierung und Testen der Beispiele fuer _scoped effects_ (1 Woche)
* Aufschrieb fuer diesen Teil (1 Woche)

--------
~ 5 Wochen


* Testen der Implementierung (higher-order) anhand von call-time choice als _scoped effect_ (optional)
* Formulierung der Gesetze als Lemma und erste Versuche fuer Beweise (optional)


# Erfolgskriterien

Da so eine Portierung (first order) bereits fuer Coq stattgefunden hat, gehen wir davon aus, dass die Punkte bis einschliesslich Punkt 5 relativ problemlos ablaufen werden.
Die Beispiele aus der vorgegebenen Arbeit sowie weitere vorgegebene Beispiele (werden im Repository dokumentiert) sollen ausfuehrbar und das gewuenschte Ergebnis liefern.
Unklar ist, ob die Portierung ins higher-order setting Fruechte traegt.
Sollte diese Portierung im Zeitrahmen nicht erreicht werden, waeren wir mit der klaren Formulierung der Problemstellung bzw. der noch zu loesenden Probleme zufrieden, wenn die folgenden 2 Punkte (Tests) nach fest definierten Einschraenkungen durchgefuehrt werden.


# Links

[1] http://hackage.haskell.org/package/polysemy
[2] http://hackage.haskell.org/package/simple-effects
[3] http://hackage.haskell.org/package/fused-effects
[4] http://hackage.haskell.org/package/extensible-effects
[5] http://hackage.haskell.org/package/freer-effects

[6] https://www.javadoc.io/doc/org.scalaz/scalaz_2.13/7.3.1/scalaz/Free.html
[7] https://github.com/b-studios/scala-effekt
[8] https://github.com/atnos-org/eff

[9] https://github.com/UlfNorell/effects
[10] Edwin Brady: Resource-Dependent Algebraic Effects (TFP 2014) https://link.springer.com/chapter/10.1007%2F978-3-319-14675-1_2

[11] Nicolas Wu et al.: Effect Handlers in Scope (Haskell 2014) http://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf
[12] Niels Bunkenburg: Modeling Call-Time Choice as Effect using Scoped Free Monads https://bunkenburg.net/papers/ModelingCallTimeChoiceAsEffect.pdf
