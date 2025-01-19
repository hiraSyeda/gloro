import json
import numpy as np
import argparse
import doitlib
from tensorflow.keras.models import Model
from tensorflow.keras.layers import Input, Flatten, Dense

def parse_arguments():
    parser = argparse.ArgumentParser()
    parser.add_argument("internal_layer_sizes", type=str)
    parser.add_argument("certifier_results", type=str)
    parser.add_argument("model_weights_csv_dir", type=str)
    parser.add_argument("input_size", type=int)
    return parser.parse_args()

def main():
    args = parse_arguments()

    INTERNAL_LAYER_SIZES = eval(args.internal_layer_sizes)
    json_results_file = args.certifier_results
    csv_loc = args.model_weights_csv_dir + "/"
    input_size = args.input_size

    print(f"Running with internal layer dimensions: {INTERNAL_LAYER_SIZES}")
    print(f"Running with input size: {input_size}")

    inputs, outputs = doitlib.build_mnist_model(Input, Flatten, Dense, input_size=input_size, internal_layer_sizes=INTERNAL_LAYER_SIZES)
    model = Model(inputs, outputs)

    print("Building zero-bias gloro model from saved weights...")

    doitlib.load_and_set_weights(csv_loc, INTERNAL_LAYER_SIZES, model)

    # evaluate hte resulting model
    print("Evaluating the resulting zero-bias gloro model...")


    x_test, y_test = doitlib.load_mnist_test_data(input_size=input_size)

    loss, accuracy = model.evaluate(x_test, y_test, verbose=2)


    print(f"Test Loss (zero bias model): {loss:.4f}")
    print(f"Test Accuracy (zero bias model): {accuracy:.4f}")


    print("Generating output vectors from the test (evaluation) data...")

    outputs = model.predict(x_test)

    predicted_classes = np.argmax(outputs, axis=1)
    true_classes = np.argmax(y_test, axis=1)

    correct_classifications = predicted_classes == true_classes

    robustness=[]
    with open(json_results_file, 'r') as f:
        robustness = json.load(f)

    print("Evaluating Verified Certified Robust Accuracy...\n")
    i=0 # robustness index
    j=0 # correct_classifications index
    count_robust_and_correct=0
    count_robust=0
    count_correct=0
    # the first item in this list is the Lipschitz bounds; others may be debug messages etc.
    assert len(robustness) >= len(correct_classifications)+1
    robustness=robustness[1:]
    assert len(robustness) >= len(correct_classifications)
    n=len(robustness)
    while i<n:
        r = robustness[i]
        if "certified" in r:
            robust = r["certified"]
            correct = correct_classifications[j]
            if robust and correct:
                count_robust_and_correct=count_robust_and_correct+1
            if robust:
                count_robust=count_robust+1
            if correct:
                count_correct=count_correct+1
            if i%1000==0:
                print(f"...done {i} of {n} evaluations...\n");
            j=j+1
        i=i+1

    assert j==10000
    assert i>=10000

    print(f"Proportion robust: {float(count_robust)/float(10000)}")
    print(f"Proportion correct: {float(count_correct)/float(10000)}")
    print(f"Proportion robust and correct: {float(count_robust_and_correct)/float(10000)}")

if __name__ == "__main__":
    main()
