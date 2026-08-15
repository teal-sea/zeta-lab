from blockpos import block_sums
import json

def run_blind_attack():
    # The scan found: kind=2, sep=18.58, d1=0.452
    # kind=2 is [('on', center, 2), ('off', center + sep, d1, 3)]
    center = 24.0
    cl = [('on', center, 2), ('off', center + 18.58, 0.452, 3)]
    r = block_sums(cl, d=48)
    blocks = r["blocks"]
    
    # blocks[0, 1] is the interaction between the on-line part and the off-line pair.
    interaction = blocks[0, 1]
    
    print("Interaction:", interaction)
    print("Is negative?", interaction < 0)
    
if __name__ == "__main__":
    run_blind_attack()
