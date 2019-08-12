# Documentation of my proofs on probabilities in Coq :)

The aim here is to prove [Kolmogorov's strong law of large numbers](https://en.wikipedia.org/wiki/Law_of_large_numbers#Strong_law).

## List of the different files

### "Measure" folder
- Measure_defs.v : measurable spaces (definitions)
  Uses Sets.v Topo_defs.v Topo_elem.v Topo_results.v
- Measure_elem.v : measurable spaces (elementary results)
  Uses Sets.v Topo_defs.v Topo_elem.v Topo_results.v Measure_defs.v 
  
### "Reals" folder
- Reals_int_def.v : real intervals (definitions)
  Uses Sets.v 
- Reals_int_elem.v : real intervals (elementary results)
  Uses Reals_int_def.v Topo_defs.v Topo_elem.v Topo_results.v
- Reals_int_results.v : real intervals (more interesting results)
  Uses Reals_int_def.v Reals_int_elem.v Topo_defs.v Topo_elem.v Topo_results.v

### "Topo" folder
- Topo_defs.v : general topology (definitions)
- Topo_elem.v : general topology (elementary results)
  Uses Topo_defs.v
- Topo_results.v : general topology (more interesting results)
  Uses Topo_defs.v Topo_elem.v
  
### "Sets_Apps" folder
- Sets_basics.v : general definitions and basic results on sets
- App_basics.v : general definitions and basic results on applications

### "Integration" folder

#### "General_integration" folder
- Integration_gen.v : general theory of integration
- Integration_reals.v : integral for real functions
#### "Kurzweil_Henstock" folder
- Kurzweil_Henstock_integral.v : KW integral (full for now, may be divided in a few files later)

### "Proba_gen" folder
- Proba_spaces_defs.v : probability spaces (definition)
- Proba_spaces_elem.v : probability spaces (elementary results)
- Proba_spaces_results.v : probability spaces (more interesting results, such as Markov inequality etc)

### "Borel_Cantelli" folder 

### Conclusion
The file Strong_law_large_numbers.v contains the result we wanted to prove !

## What do I use ?

Almost nothing : 
```
Require Import Classical.
Require Import ClassicalChoice.
Require Import ClassicalDescription.
Require Import Description.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import List.
Require Import Psatz.
Require Import Rbase.
Require Import Rfunctions.
```
