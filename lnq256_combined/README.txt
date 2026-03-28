lnQ256 relaxed-bounds implementation
====================================

The active design no longer tries to compute exact `floor(ln(x) * 2^256)`.
Instead, it shares one arithmetic skeleton for both one-sided bounds:

- lower in `[floor(y) - 1, floor(y)]`
- upper in `[ceil(y), ceil(y) + 1]`

where `y = ln(x) * 2^256`.

Active kernel
-------------

- 16-bucket coarse reduction with the shared `N0` table
- `z = u / (2 + u)`, `w = z^2`
- explicit odd terms through `z^5`
- deferred residual `z^7 * P(w) / Q(w)`
- rational degrees `[6/7]`
- coefficient precision `Q219`
- guard bits `G = 9`
- one global additive bias and one global radius

Active files
------------

- `lnq256_common.py`: shared arithmetic helpers and coarse-state extraction
- `lnq256_case_battery.py`: shared random/adversarial battery builders
- `lnq256_stage1_q216_reference.py`: old Q216/G24 fast-path constants retained only as search baselines
- `lnq256_model_stage1_z5_global.py`: executable relaxed bounds model
- `lnq256_search_stage1_relaxed.py`: search/calibration harness
- `lnq256_test_stage1_z5_global.py`: validation battery

Validation
----------

- `python3 lnq256_combined/lnq256_test_stage1_z5_global.py --random-cases 50000 --boundary-cases 10000 --seeds 1 2 3`
