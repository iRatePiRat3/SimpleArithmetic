====================================================================================================
DETAILED TRACE: n = 31 (AS YOUR EXAMPLE)
====================================================================================================

───────────────────────────────────────────────���────────────────────────────────────────────────────
STEP 0: n = 31
────────────────────────────────────────────────────────────────────────────────────────────────────

Initial Decomposition (ℓ = 5, B = 32):
  1 full boxes + 31 units in partial box
  = 1 × 32 + 31

After Tripling (×3):
  Full boxes: 3
  Fractional units: 93

After Adding 1:
  Full boxes: 3
  Fractional units: 94

Division Phase (÷ 2^1):
  Full boxes after division: 3/2
  Fractional units after division: 47

Next Value n' = 47
Next Decomposition (ℓ = 5, B = 32):
  1 full boxes + 15 units

────────────────────────────────────────────────────────────────────────────────────────────────────
STEP 1: n = 47
────────────────────────────────────────────────────────────────────────────────────────────────────

Initial Decomposition (ℓ = 4, B = 16):
  2 full boxes + 15 units in partial box
  = 2 × 16 + 15

After Tripling (×3):
  Full boxes: 6
  Fractional units: 45

After Adding 1:
  Full boxes: 6
  Fractional units: 46

Division Phase (÷ 2^1):
  Full boxes after division: 3
  Fractional units after division: 23

Next Value n' = 71
Next Decomposition (ℓ = 5, B = 32):
  2 full boxes + 7 units

────────────────────────────────────────────────────────────────────────────────────────────────────
STEP 2: n = 71
────────────────────────────────────────────────────────────────────────────────────────────────────

Initial Decomposition (ℓ = 5, B = 32):
  2 full boxes + 7 units in partial box
  = 2 × 32 + 7

After Tripling (×3):
  Full boxes: 6
  Fractional units: 21

After Adding 1:
  Full boxes: 6
  Fractional units: 22

Division Phase (÷ 2^1):
  Full boxes after division: 3
  Fractional units after division: 11

Next Value n' = 107
Next Decomposition (ℓ = 6, B = 64):
  1 full boxes + 43 units

────────────────────────────────────────────────────────────────────────────────────────────────────
STEP 3: n = 107
────────────────────────────────────────────────────────────────────────────────────────────────────

Initial Decomposition (ℓ = 6, B = 64):
  1 full boxes + 43 units in partial box
  = 1 × 64 + 43

After Tripling (×3):
  Full boxes: 3
  Fractional units: 129

After Adding 1:
  Full boxes: 3
  Fractional units: 130

Division Phase (÷ 2^1):
  Full boxes after division: 3/2
  Fractional units after division: 65

Next Value n' = 161
Next Decomposition (ℓ = 6, B = 64):
  2 full boxes + 33 units

────────────────────────────────────────────────────────────────────────────────────────────────────
STEP 4: n = 161
────────────────────────────────────────────────────────────────────────────────────────────────────

Initial Decomposition (ℓ = 6, B = 64):
  2 full boxes + 33 units in partial box
  = 2 × 64 + 33

After Tripling (×3):
  Full boxes: 6
  Fractional units: 99

After Adding 1:
  Full boxes: 6
  Fractional units: 100

Division Phase (÷ 2^1):
  Full boxes after division: 3
  Fractional units after division: 50

Next Value n' = 242
Next Decomposition (ℓ = 1, B = 2):
  121 full boxes + 0 units

────────────────────────────────────────────────────────────────────────────────────────────────────
STEP 5: n = 242
────────────────────────────────────────────────────────────────────────────────────────────────────

Initial Decomposition (ℓ = 1, B = 2):
  121 full boxes + 0 units in partial box
  = 121 × 2 + 0

After Tripling (×3):
  Full boxes: 363
  Fractional units: 0

After Adding 1:
  Full boxes: 363
  Fractional units: 1

Division Phase (÷ 2^1):
  Full boxes after division: 181.5
  Fractional units after division: 0.5

Next Value n' = 363
Next Decomposition (ℓ = 1, B = 2):
  181 full boxes + 1 units

════════════════════════════════════════════════════════════════════════════════════════════════════
TRAJECTORY ANALYSIS
════════════════════════════════════════════════════════════════════════════════════════════════════

════════════════════════════════════════════════════════════════════════════════════════════════════
n = 31
════════════════════════════════════════════════════════════════════════════════════════════════════
Steps to convergence: 17

Fractional Box Content Statistics:
  Mean fractional content: 0.651154
  Max fractional content:  0.971252
  Min fractional content:  0.000000

Box Level Transitions:
  Level increases (ℓ ↑): 3
  Level increases (ℓ ↓): 7
  Level stable (ℓ =):    7

Overflow Events (fractional > box size):
  Count: 4 / 17

Fractional Box Content Statistics:
  Mean fractional content: 0.651154
  Max fractional content:  0.971252
  Min fractional content:  0.000000

First 15 steps:
Step |      n | ℓ |  Full |   Frac |  After÷2 Full |  After÷2 Frac |      n' | ℓ'
     |   31 |  5 |   1.0 |  31.00 |           1.5 |         47.00 |       47 |  4
   1 |   47 |  4 |   2.0 |  15.00 |           3.0 |         23.00 |       71 |  5
   2 |   71 |  5 |   2.0 |   7.00 |           3.0 |         11.00 |      107 |  6
   3 |  107 |  6 |   1.0 |  43.00 |           1.5 |         65.00 |      161 |  6
   4 |  161 |  6 |   2.0 |  33.00 |           3.0 |         50.00 |      242 |  1
   5 |  242 |  1 |  121.0 |   0.00 |         181.5 |          0.50 |      363 |  1
   6 |  363 |  1 |  181.0 |   1.00 |         272.5 |          1.50 |      545 |  2
   7 |  545 |  2 |  136.0 |   1.00 |         204.0 |          2.00 |      409 |  0
   8 |  409 |  0 |   0.0 | 409.00 |         181.5 |        204.50 |      364 |  2
   9 |  364 |  2 |   91.0 |   0.00 |         136.5 |          0.75 |      273 |  4
  10 |  273 |  4 |   17.0 |   1.00 |         127.5 |          8.50 |      256 |  8
  11 |  256 |  8 | 1.0 |  0.00 |           0.5 |          0.25 |       128 |  7
  12 |  128 |  7 |   1.0 |   0.00 |           0.5 |          0.25 |        64 |  6
  13 |   64 |  6 |   1.0 |   0.00 |           0.5 |          0.25 |        32 |  5
  14 |   32 |  5 |   1.0 |   0.00 |           0.5 |          0.25 |        16 |  4

════════════════════════════════════════════════════════════════════════════════════════════════════
n = 27
════════════════════════════════════════════════════════════════════════════════════════════════════
Steps to convergence: 111

Fractional Box Content Statistics:
  Mean fractional content: 0.497835
  Max fractional content:  0.999390
  Min fractional content:  0.000000

Box Level Transitions:
  Level increases (ℓ ↑): 26
  Level increases (ℓ ↓): 47
  Level increases (ℓ =):    38

Overflow Events (fractional > box size):
  Count: 28 / 111

Fractional Box Content Statistics:
  Mean fractional content: 0.497835
  Max fractional content:  0.999390
  Min fractional content:  0.000000

Box Level Transitions:
  Level increases (ℓ ↑): 26
  Level increases (ℓ ↓): 47
  Level increases (ℓ ↓): 38

First 15 steps:
Step |      n | ℓ |  Full |   Frac |  After÷2 Full |  After÷2 Frac |      n' | ℓ'
     |   27 |  1 |   13.0 |   1.00 |          39.5 |          1.50 |       79 |  6
   1 |   79 |  6 |   1.0 |  15.00 |           1.5 |         23.00 |       47 |  4
   2 |   47 |  4 |   2.0 |  15.00 |           3.0 |         23.00 |       71 |  5
   3 |   71 |  5 |   2.0 |   7.00 |           3.0 |         11.00 |      107 |  6
   4 |  107 |  6 |   1.0 |  43.00 |           1.5 |         65.00 |      161 |  6
   5 |  161 |  6 |   2.0 |  33.00 |           3.0 |         50.00 |      242 |  1
   6 |  242 |  1 |  121.0 |   0.00 |         181.5 |          0.50 |      363 |  1
   7 |  363 |  1 |  181.0 |   1.00 |         272.5 |          1.50 |      545 |  2
   8 |  545 |  2 |  136.0 |   1.00 |         204.0 |          2.00 |      409 |  0
   9 |  409 |  0 |   0.0 | 409.00 |         181.5 |        204.50 |      364 |  2
  10 |  364 |  2 |   91.0 |   0.00 |         136.5 |          0.75 |      273 |  4
  11 |  273 |  4 |   17.0 |   1.00 |         127.5 |          8.50 |      256 |  8
  12 |  256 |  8 |   1.0 |   0.00 |           0.5 |          0.25 |      128 |  7
  13 |  128 |  7 |   1.0 |   0.00 |         0.5 |          0.25 |        64 |  6
  14 |   64 |  6 |   1.0 |   0.00 |           0.5 |          0.25 |        32 |  5

════════════════════════════════════════════════════════════════════════════════════════════════════
n = 231
════════════════════════════════════════════════════════════════════════════════════════════════════
Steps to convergence: 57

Fractional Box Content Statistics:
  Mean fractional content: 0.487926
  Max fractional content:  0.996094

Box Level Transitions:
  Level increases (ℓ ↑): 11
  Level increases (ℓ ↓): 26
  Level increases (ℓ =):    20

Overflow Events (fractional > box size):
  Count: 11 / 57

Fractional Box Content Statistics:
  Mean fractional content: 0.487926
  Max fractional content:  0.996094

Overflow Events (fractional > box size):
  Count: 11 / 57

First 15 steps:
Step |      n | ℓ |  Full |   Frac |  After÷2 Full |  After÷2 Frac |      n' | ℓ'
     |  231 |  5 |   7.0 |   7.00 |          10.5 |         11.00 |      347 |  1
   1 |  347 |  1 |  173.0 |   1.00 |         259.5 |          1.50 |      519 |  2
   2 |  519 |  2 |  129.0 |   3.00 |         193.5 |          4.50 |      581 |  0
   3 |  581 |  0 |   0.0 | 581.00 |         870.5 |        870.50 |      870 |  1
   4 |  870 |  1 |  435.0 |   0.00 |         652.5 |          0.75 |     1305 |  0
   5 | 1305 |  0 |   0.0 |1305.00 |        1957.5 |       1957.50 |     1956 |  2
   6 | 1956 |  2 |  489.0 |   0.00 |         733.5 |          1.13 |     1467 |  1
   7 | 1467 |  1 |  733.0 |   1.00 |        1100.0 |          2.00 |     2200 |  4
   8 | 2200 |  4 |  137.0 |   8.00 |         205.5 |         12.00 |      329 |  0
   9 |  329 |  0 |   0.0 | 329.00 |         493.5 |        493.50 |      494 |  1
  10 |  494 |  1 |  247.0 |   0.00 |         370.5 |          0.75 |      741 |  0
  11 |  741 |  0 |   0.0 | 741.00 |        1111.5 |       1111.50 |     1112 |  4
  12 | 1112 |  4 |   69.0 |   8.00 |         103.5 |         12.00 |      207 |  4
  13 |  207 |  4 |   12.0 |  15.00 |          18.0 |         22.50 |       87 |  6
  14 |   87 |  6 |   1.0 |  23.00 |           1.5 |         34.50 |      131 |  0

════════════════════════════════════════════════════════════════════════════════════════════════════
n = 3077
════════════════════════════════════════════════════════════════════════════════════════════════════
Steps to convergence: 22

Fractional Box Content Statistics:
  Mean fractional content: 0.565752
  Max fractional content:  0.951172

Box Level Transitions:
  Level increases (ℓ ↑): 6
  Level increases (ℓ ↓): 8
  Level increases (ℓ =):    8

Overflow Events (fractional > box size):
  Count: 5 / 22

Fractional Box Content Statistics:
  Mean fractional content: 0.565752
  Max fractional content:  0.951172

Overflow Events (fractional > box size):
  Count: 5 / 22

First 15 steps:
Step |      n | ℓ |  Full |   Frac |  After÷2 Full |  After÷2 Frac |      n' | ℓ'
     | 3077 |  6 |  48.0 |  13.00 |          72.0 |         19.50 |     4615 |  0
   1 | 4615 |  0 |   0.0 |4615.00 |        6922.5 |       6922.50 |     6924 |  2
   2 | 6924 |  2 |   1731.0 |   0.00 |        2596.5 |          1.13 |     5193 |  0
   3 | 5193 |  0 |   0.0 |5193.00 |        7789.5 |       7789.50 |     7790 |  1
   4 | 7790 |  1 |   3895.0 |   0.00 |        5842.5 |          0.75 |    11685 |  0
   5 |11685 |  0 |   0.0 |11685.00 |       17527.5 |      17527.50 |    17528 |  2
   6 |17528 |  2 |   4382.0 |   0.00 |        6573.0 |          1.50 |    13146 |  1
   7 |13146 |  1 |   6573.0 |   0.00 |        9859.5 |          0.75 |    19719 |  0
   8 |19719 |  0 |   0.0 |19719.00 |       29578.5 |      29578.50 |    29580 |  2
   9 |29580 |  2 |   7395.0 |   0.00 |       11092.5 |          1.13 |    22185 |  0
  10 |22185 |  0 |   0.0 |22185.00 |       33277.5 |      33277.50 |    33280 |  5
  11 |33280 |  5 |   1040.0 |   0.00 |        1560.0 |          1.25 |     3120 |  4
  12 | 3120 |  4 |    195.0 |   0.00 |         292.5 |          0.75 |      585 |  0
  13 |  585 |  0 |   0.0 | 585.00 |         877.5 |        877.50 |      878 |  1
  14 |  878 |  1 |   439.0 |   0.00 |         658.5 |          0.75 |     1317 |  0
