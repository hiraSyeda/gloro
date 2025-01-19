import numpy as np
import argparse

def mprint(string):
    print(string, end="")

def parse_arguments():
    parser = argparse.ArgumentParser()
    parser.add_argument("internal_layer_sizes", type=str)
    parser.add_argument("model_weights_csv_dir", type=str)
    return parser.parse_args()

def main():
    args = parse_arguments()

    INTERNAL_LAYER_SIZES = eval(args.internal_layer_sizes)
    csv_loc = args.model_weights_csv_dir + "/"

    weights = []
    i=0
    # always one extra iteration than INTERNAL_LAYER_SIZES length
    while i<=len(INTERNAL_LAYER_SIZES):
        weights.append(np.loadtxt(csv_loc+f"layer_{i}_weights.csv", delimiter=",").tolist())
        i=i+1

    m = 0

    weightslen=len(weights)
    w=0
    for mat in weights:
        #print(f"Matrix {m} has dimensions: {len(mat)} x {len(mat[0])}")
        m = m + 1

        mprint("[")
        matlen=len(mat)
        r=0
        for row in mat:
            mprint("[")
            count=0
            n=len(row)
            for num in row:
                mprint(f"{num:.5f}")
                count=count+1
                if count<n:
                    mprint(",")
            mprint("]")
            r=r+1
            if r<matlen:
                mprint(",")
        mprint("]")
        w=w+1
        if w<weightslen:
            mprint(",")

if __name__ == "__main__":
    main()