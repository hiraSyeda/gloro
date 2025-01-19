import argparse
import sys

from tensorflow.keras.layers import Input, Flatten, Dense
from tensorflow.keras.models import Model

from doitlib import printlist, build_mnist_model, load_and_set_weights, load_mnist_test_data


def parse_arguments():
    parser = argparse.ArgumentParser()
    parser.add_argument("internal_layer_sizes", type=str)
    parser.add_argument("model_weights_csv_dir", type=str)
    parser.add_argument("output_file", type=str)
    parser.add_argument("input_size", type=int)
    return parser.parse_args()

def main():
    args = parse_arguments()

    INTERNAL_LAYER_SIZES = eval(args.internal_layer_sizes)
    csv_loc = args.model_weights_csv_dir + "/"
    output_file = args.output_file
    input_size = args.input_size

    print(f"Running with internal layer dimensions: {INTERNAL_LAYER_SIZES}")
    print(f"Running with input_size: {input_size}")

    inputs, outputs = build_mnist_model(
        Input,
        Flatten,
        Dense,
        input_size=input_size,
        internal_layer_sizes=INTERNAL_LAYER_SIZES)

    model = Model(inputs, outputs)

    print("Building zero-bias gloro model from saved weights...")
    load_and_set_weights(csv_loc, INTERNAL_LAYER_SIZES, model)

    print("Evaluating the resulting zero-bias gloro model...")
    x_test, y_test = load_mnist_test_data(input_size=input_size)
    loss, accuracy = model.evaluate(x_test, y_test, verbose=2)

    print(f"Test Loss (zero bias model): {loss:.4f}")
    print(f"Test Accuracy (zero bias model): {accuracy:.4f}")

    print("Generating output vectors from the test (evaluation) data...")
    outputs = model.predict(x_test)
    n=len(outputs)
    num_samples=n

    # Check if input is in the range
    if 0 <= num_samples <= n:
        saved_stdout=sys.stdout
        with open(output_file,'w') as f:
            sys.stdout=f
            for i in range(num_samples):
                test_output = outputs[i].tolist()
                printlist(test_output)
        sys.stdout=saved_stdout
    else:
        print("Invalid number entered. No outputs for you!")

if __name__ == "__main__":
    main()