"""AIMO Interpretability submission -- official all-False reference / control.

The organizers own constant baseline. Reproduces accuracy 0.6786 (19/28),
coverage 1.0, 0 invalid on the public val-sample through the official
ingestion+scoring path. Included as the report control and as a conservative
alternative if the hidden test resembles the curated val-sample rather than
the natural public distribution.
"""


def are_robust(model_id: str, problems: list) -> list:
    del model_id
    return [False for _ in problems]
