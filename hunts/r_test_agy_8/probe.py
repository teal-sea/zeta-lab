import json
import sys
import mpmath

from zeta.explicit import li

def main():
    mpmath.mp.dps = 15
    # Calculate the logarithmic integral for a few values
    results = {}
    for x in [10, 100, 1000]:
        val = li(x)
        results[str(x)] = str(val)
    
    with open("hunts/r_test_agy_8/results.json", "w") as f:
        json.dump(results, f, indent=2)

if __name__ == "__main__":
    main()
