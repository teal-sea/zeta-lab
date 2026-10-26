import importlib.util, json, io, contextlib
import numpy as np
def load():
    spec=importlib.util.spec_from_file_location('th','hunts/lambda_dh_exact/theory.py'); th=importlib.util.module_from_spec(spec); spec.loader.exec_module(th); return th
fix={114.1633:0.1508301, 166.4793:0.0743561, 176.7025:0.2242577, 240.4046:0.3695306}
out={}
for label in ('recorded','corrected'):
    th=load()
    if label=='corrected':
        th.NINE=[(g, fix.get(g,y), t) for g,y,t in th.NINE]
    with contextlib.redirect_stdout(io.StringIO()):
        th.stage5()
    cal=th.RESULTS['calibration']
    anchor = 0.3695261 if label=='recorded' else 0.3695306
    sup={}
    for p in (0.5,1.0,1.5,2.0):
        cp=(1-anchor/th.DELTA)*th.L(600)**p
        grid=(600,3e3,1e4,1e5,1e6,1e8,1e12,1e20)
        rows=[(g,th.DELTA*(1-cp/th.L(g)**p)) for g in grid]
        rows=[(g,y,th.t_star_gap(y,g)) for g,y in rows if y>0]
        b=max(rows,key=lambda r:r[2])
        sup[str(p)]=dict(y_max_1e4=th.DELTA*(1-cp/th.L(1e4)**p), sup=b[2])
    out[label]=dict(d_over_h_mean=cal['mean'], d_over_h_sd=cal['sd'], training_ratio=cal['training_ratio'], sup=sup)
rec=json.load(open('hunts/lambda_dh_exact/theory_results.json'))
out['theory_results_mean_check']=rec['calibration']['mean']
json.dump(out, open('hunts/lambda_dh_exact/slip_effect.json','w'), indent=2)
r,c=out['recorded'],out['corrected']
print('d/h mean', r['d_over_h_mean'], c['d_over_h_mean'], 'artifact', out['theory_results_mean_check'])
for p in r['sup']: print(p, r['sup'][p], c['sup'][p])
