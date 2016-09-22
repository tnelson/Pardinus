# Pardinus

Pardinus - Kodkod's (slightly bulkier) Iberian cousin

This repository includes the source code for the Pardinus solver, an extension to the [Kodkod](http://alloy.mit.edu/kodkod/index.html) solver for relational logic. It extends Kodkod with the following functionalities:
* Target-oriented and weighted-target oriented model finding (@tmguimaraes, @nmacedo, @alcinocunha);
* Decomposed parallelized model finding (@EduardoPessoa, @nmacedo, @alcinocunha);
* Model finding over temporal relational formulas (@EduardoPessoa, @nmacedo, @alcinocunha);
* Support for unbounded relational model finding (planned).

Pardinus is open-source and available under the [MIT license](LICENSE), as is Kodkod. However, the implementation relies on third-party SAT solvers ([SAT4J](http://www.sat4j.org), [MiniSat](http://minisat.se), [Glucose](http://www.labri.fr/perso/lsimon/glucose/), and [(P)Lingeling](http://fmv.jku.at/lingeling/)), some of which are released under stricter licenses. Please see the solver licenses for details.
