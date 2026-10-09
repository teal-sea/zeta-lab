# What the KLN source addendum changes

The public proof at `6b120d1f` applies KLN Lemma4.14 and its Table1. No invalid application, incorrect table row, or false density inequality was identified. The separate introductory-Theorem1.1 parameter issue was already resolved by using Lemma4.14. Accepting the cited density lemma as a published input, this audit has not found a gap in the seventh-power derivation itself.

The additional check concerns the justification upstream of that cited lemma. Johnston-Yang records a real defect in the historical critical-line source. Hiary-Patel-Yang later restores the required bound. Also, KLN's printed low-height estimate1.461 is insufficient to justify its rounded a2=2.851 by the displayed argument. Our earlier source audit did not document either point, so its claim of complete source acceptance was too broad.

This is therefore a substantive completion of the source justification, not merely formatting or a new bibliographic label. HPY supplies the high-height bound; the independent Acb enclosure on[0,3] supplies the previously unproved small-height implication in that printed argument. Together they recover the exact inputs a1=.63,a2=2.851. We do not claim that the density rows are false or that their numerical constants have been independently recomputed.

The addendum leaves the theorem statement, density rows, prime-interval calculations and existing checker unchanged. It supports continued acceptance of the written conditional result. Calling the whole public prime-interval proof refuted or mathematically invalid would overstate the finding; calling the added low-height proof mere citation cleanup would understate it.

See [the exact source argument](SOURCE-CHECK.md), [the new reproducer](check_low.py) and [its output](check_low.txt). No formal verification or audit of every external theorem is claimed.
