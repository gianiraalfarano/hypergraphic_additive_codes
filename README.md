# Additive codes arising from hypergraphs: computations

This repository contains the SageMath program behind Section 6 of the paper

> Gianira N. Alfarano, *Additive codes arising from hypergraphs*, 2026.

The program computes every entry of Tables 2, 3, 4 and 5 of the paper and checks that it agrees with the value printed there. It also checks the statements about these tables made in the text.

## Files

| File | What it is |
|---|---|
| `section6.py` | the program |
| `output.txt` | what the program prints (full run with SageMath 10.8) |
| `LICENSE` | the licence (MIT: you can use and modify the code freely) |

## How to run it

1. Install [SageMath](https://www.sagemath.org) (any recent version).
2. Open a terminal in the folder that contains `section6.py` and type

   ```
   sage section6.py
   ```

   This takes about 20 minutes. The last line says whether all values agree with the paper.

Other options:

```
sage section6.py --quick     # about 4 minutes: skips the slowest part (the split Cayley hexagon)
sage section6.py 5           # only Table 5 (you can give any of 2, 3, 4, 5)
```

Without SageMath, the program also runs with Python and the pip version of SageMath (passagemath):

```
pip install passagemath-repl passagemath-graphs passagemath-polyhedra passagemath-combinat passagemath-gap passagemath-flint passagemath-pari
python section6.py
```

## What is computed

- **Table 2.** For 16 hypergraphs H (complete hypergraphs, the Fano plane, affine and projective planes, generalised quadrangles, the split Cayley hexagon, ...): the dual distance and the minimum distance of the code C_H, which are the Berge girth and the edge-connectivity of H, and the lower and upper bounds on the minimum distance compared in the paper.
- **Table 3.** The weak chromatic number of H, the critical exponent of C_H for q = 2, and its bounds.
- **Table 4.** Spread codes, the hexacode and two codes found by S. Kurz (included in the program): minimum distance, dual distance, critical exponent and bounds.
- **Table 5.** Upper bounds on n_2(k,2;s), the largest length of an additive code over F_4 with F_2-dimension k and n - d <= s, for k = 5, 6, 7, 8. The exact values of n_2(k,2;s) are taken from S. Kurz, *Additive codes attaining the Griesmer bound*, arXiv:2412.14615, Theorems 12-15.

The linear programming bounds are solved exactly, with rational numbers (the `PPL` solver of SageMath), because solvers that use decimal approximations can give wrong answers for these systems.

## Contact

Gianira N. Alfarano, Université de Rennes, IRMAR (gianira-nicoletta.alfarano@univ-rennes.fr).

If you use this code, please cite the paper above.
