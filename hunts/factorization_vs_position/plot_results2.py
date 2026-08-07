import json
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

def main():
    results_path = os.path.join(os.path.dirname(__file__), "results2.json")
    if not os.path.exists(results_path):
        print("Results file not found.")
        return
        
    with open(results_path, "r") as f:
        results = json.load(f)
        
    x = [r["factorization_defect"] for r in results]
    y = [r["max_position_residue"] for r in results]
    labels = []
    for r in results:
        if r["discriminant"] == 0:
            labels.append("Zeta (Control)")
        else:
            labels.append(f"D={r['discriminant']} Form={tuple(r['form'])}")
            
    plt.figure(figsize=(10, 6))
    plt.scatter(x, y, color='blue')
    
    for i, label in enumerate(labels):
        plt.annotate(
            label, 
            (x[i], y[i]), 
            textcoords="offset points", 
            xytext=(0,10), 
            ha='center'
        )
        
    plt.xlabel("Factorization Defect $D(F)$")
    plt.ylabel("Max Absolute Weil Position Residue $R_F$")
    plt.title("Epstein Zeta: Factorization Defect vs Weil Position Residue (Principal Forms)")
    plt.grid(True, linestyle='--', alpha=0.7)
    
    out_path = os.path.join(os.path.dirname(__file__), "correlation_plot.png")
    plt.savefig(out_path, dpi=300, bbox_inches='tight')
    print(f"Plot saved to {out_path}")

if __name__ == "__main__":
    main()
