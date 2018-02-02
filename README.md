Pardinus
=======

Pardinus is Kodkod's (slightly bulkier) Iberian cousin

This repository includes the source code for the Pardinus solver, an extension to the [Kodkod](http://alloy.mit.edu/kodkod/index.html) solver for relational logic. It extends Kodkod with the following functionalities:
* Target-oriented and weighted-target oriented model finding
* Model finding over temporal relational formulas
* Decomposed parallelized model finding
* Support for unbounded relational model finding

Pardinus is developed at the High-Assurance Software Laboratory ([HASLab](http://haslab.di.uminho.pt)), from INESC TEC and University of Minho, and is led by Alcino Cunha and Nuno Macedo. It is used as a back-end for [Electrum Analyzer](), an extension to the Alloy Analyzer.

Pardinus is open-source and available under the [MIT license](LICENSE), as is Kodkod. However, the implementation relies on third-party solvers ([SAT4J](http://www.sat4j.org), [MiniSat](http://minisat.se), [Glucose/Syrup](http://www.labri.fr/perso/lsimon/glucose/), [(P)Lingeling](http://fmv.jku.at/lingeling/), and [Yices](http://yices.csl.sri.com)), some of which are released under stricter licenses (see the various LICENSE files in the distribution for details)

Pardinus can be built and run following the instructions from [Kodkod](https://github.com/emina/kodkod/blob/master/README.md#building-and-installing-kodkod).

## Collaborators
- Alcino Cunha, 2013 - present
- Nuno Macedo, 2013 - present
- Tiago Guimarães, 2013 - 2014
- Eduardo Pessoa, 2015 - 2016

## History
### Pardinus (1.0) (January 2017)
<!--- FM 18 -->
- Support for unbounded model finding in SMV through [Electrod](https://github.com/grayswandyr/electrod/releases/tag/0.1)
- Support for [Electrum Analyzer 1.0](https://github.com/haslab/Electrum/releases/tag/v1.0)

### Pardinus (0.3.1) (September 2016) 
<!--- TACAS 17 -->
- Support for symbolic bounds on decomposed model finding

### Pardinus (0.3.0) (September 2016) 
<!--- TRUST Workshop 16 -->
- Initial support for temporal model finding
- Support for [Electrum Analyzer 0.2]()

### Pardinus (0.2.0) (April 2016) 
<!--- ASE16 submission -->
- Initial support for decomposed model finding
- Support for Syrup (parallel Glucose)

### Pardinus (0.1.1) (October 2014) 
<!--- FASE15 submission -->
- Support for weighted target-oriented model finding
- Merged Alloy Analyzer's Kodkod 2.0 tweaks into Kodkod 2.1
- Supported scenario exploration operations from [extended Alloy Analyzer](toalloy.jar)
- Described in the FASE 15 [paper](http://dx.doi.org/10.1007/978-3-662-46675-9_20)

### Pardinus (0.1.0) (October 2013) 
<!--- FASE14 submission -->
- Initial support for target-oriented model finding
- Extended support to Max-SAT SAT4J and Yices
- Described in the FASE 14 [paper](http://dx.doi.org/10.1007/978-3-642-54804-8_2)

