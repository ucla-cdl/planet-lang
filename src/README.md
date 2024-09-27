# Overview

## Files
`expdesdsl`: Repo with R package under development

`classes.Rmd`: Incomplete sketch of classes to include in a R library

`wu-simulator.Rmd`: File sketching out how to "simulate" data for Wu et al. UIST 2023 paper

## SETUP: How to develop R package locally (adapted from https://r-pkgs.org/setup.html)
MAC OS
0. Install R: 
    `brew install r`
1. Install dependencies:
    `brew install harffbuzz`
    `brew install harffbuzz`
    `brew install libgit2`
    `brew install libtiff`
1. Install packages for developing R packages. In R terminal: 
    `install.packages(c("devtools", "roxygen2", "testthat", "knitr"))`
2. Import devtools package in R terminal:
    `library(devtools)`
3. Load expdesdsl library locally: 
    `devtools::load_all()`


## Writing and running tests
Any changes made to the package's source code needs to be reloaded locally. So, here is a recommended this workflow: 
1. Make changes to source. 
2. Reload package locally: `devtools::load_all()`
3. Add tests
4. Run tests: `devtools::test()`

TIPS
Added a new source file (e.g., for a class)? Time to add a new test file! Run this command while the the new file is in "focus" (i.e., cursor is in thew new file): `usethis::use_test()` 