import math
S5 = math.sqrt(5)
vals = {
 "c_phi generic 1-2/sqrt5": 1-2/S5,
 "second 4/sqrt5-1": 4/S5-1,
 "b2 9/(4sqrt5)-1": 9/(4*S5)-1,
 "b2 second 1-7/(4sqrt5)": 1-7/(4*S5),
 "b3 1-20/(9sqrt5)": 1-20/(9*S5),
 "b3 second 22/(9sqrt5)-1": 22/(9*S5)-1,
 "b4 1-35/(16sqrt5)": 1-35/(16*S5),
 "b5 56/(25sqrt5)-1": 56/(25*S5)-1,
 "b5 second 1-54/(25sqrt5)": 1-54/(25*S5),
 "b6 1-79/(36sqrt5)": 1-79/(36*S5),
 "22/7-e 110/(49sqrt5)-1": 110/(49*S5)-1,
 "22/7-e second 1-108/(49sqrt5)": 1-108/(49*S5),
 "(1+e)/6 7/(3sqrt5)-1": 7/(3*S5)-1,
 "(1+e)/6 second 1-sqrt5/3": 1-S5/3,
 "(1+e)/3 1-2/sqrt5": 1-2/S5,
 "(1+e)/3 second 8/(3sqrt5)-1": 8/(3*S5)-1,
}
paper = {
 "c_phi generic 1-2/sqrt5": 0.105572809000,
 "second 4/sqrt5-1": None,
 "b2 9/(4sqrt5)-1": 0.006230589875,
 "b2 second 1-7/(4sqrt5)": 0.217376207875,
 "b3 1-20/(9sqrt5)": 0.0061920100000935,
 "b3 second 22/(9sqrt5)-1": 0.0931887889998972,
 "b4 1-35/(16sqrt5)": 0.0217202598438420,
 "b5 56/(25sqrt5)-1": 0.0017584539199058,
 "b5 second 1-54/(25sqrt5)": 0.0340186337200909,
 "b6 1-79/(36sqrt5)": 0.0186146098750923,
 "22/7-e 110/(49sqrt5)-1": None,
 "22/7-e second 1-108/(49sqrt5)": None,
 "(1+e)/6 7/(3sqrt5)-1": 0.043498389500,
 "(1+e)/6 second 1-sqrt5/3": 0.2546440075,
 "(1+e)/3 1-2/sqrt5": 0.105572809000,
 "(1+e)/3 second 8/(3sqrt5)-1": 0.192569588000,
}
for k,v in vals.items():
    p = paper[k]
    flag = "" if p is None else ("OK" if abs(v-p) < 1e-9 else "MISMATCH")
    print(f"{k} = {v:.12f}  paper={p}  {flag}")
