from hunts.gabcke_remainder.coefficients import PRINTED, lambdas, matches_printed


def test_lambda_recursion_matches_the_printed_values() -> None:
    assert matches_printed()
    assert lambdas(6) == list(PRINTED)
