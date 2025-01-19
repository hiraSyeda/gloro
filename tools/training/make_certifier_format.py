import numpy as np
import argparse
from doitlib import format_weights

def parse_arguments():
    parser = argparse.ArgumentParser()
    parser.add_argument("internal_layer_sizes", type=str)
    parser.add_argument("model_weights_csv_dir", type=str)
    return parser.parse_args()

def main():
    args = parse_arguments()

    INTERNAL_LAYER_SIZES = eval(args.internal_layer_sizes)
    csv_loc = args.model_weights_csv_dir + "/"

    # always one extra iteration than INTERNAL_LAYER_SIZES length
    weights = [
        np.loadtxt(csv_loc + f"layer_{i}_weights.csv", delimiter=",").tolist()
        for i in range(len(INTERNAL_LAYER_SIZES) + 1)
    ]

    format_weights(weights)

if __name__ == "__main__":
    main()