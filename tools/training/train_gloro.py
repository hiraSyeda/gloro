import argparse
import os

import numpy as np
import tensorflow as tf
from tensorflow.keras import backend as K

from doitlib import resize_image, build_mnist_model
from gloro.layers import Dense, Flatten, Input
from gloro.models import GloroNet
from gloro.training import losses
from gloro.training.callbacks import (
    EpsilonScheduler, LrScheduler, TradesScheduler)
from gloro.utils import print_if_verbose
from utils import get_data, get_optimizer

# Suppress TensorFlow info/warnings
os.environ['TF_CPP_MIN_LOG_LEVEL'] = '3'


def train_gloro(
        dataset,
        epsilon,
        epsilon_schedule='fixed',
        loss='crossentropy',
        augmentation='standard',
        epochs=None,
        batch_size=None,
        optimizer='adam',
        lr=0.001,
        lr_schedule='fixed',
        trades_schedule=None,
        verbose=False,
        INTERNAL_LAYER_SIZES=[64],
        input_size=28
):
    _print = print_if_verbose(verbose)

    # Load data and set up data pipeline.
    _print('loading data...')

    train, test, metadata = get_data(dataset, batch_size=256, augmentation='none')

    if dataset.lower() == "mnist":  # Ensure case insensitivity
        if input_size != 28:
            train = train.map(resize_image(input_size))
            test = test.map(resize_image(input_size))

        # Create the model.
        _print('creating model...')

        inputs, outputs = build_mnist_model(
            Input,
            Flatten,
            Dense,
            input_size=input_size,
            internal_layer_sizes=INTERNAL_LAYER_SIZES)

    else:
        # Handle other datasets if required
        print(f"Dataset '{dataset}' is not supported for this specific configuration.")
        return None

    g = GloroNet(inputs, outputs, epsilon)

    if verbose:
        g.summary()

    # Compile and train the model.
    _print('compiling model...')

    g.compile(
        loss=losses.get(loss),
        optimizer=get_optimizer(optimizer, lr),
        metrics=[tf.keras.metrics.SparseCategoricalAccuracy()]
    )

    print('training model...')
    g.fit(
        train,
        epochs=epochs,
        validation_data=test,
        callbacks=[
                      EpsilonScheduler(epsilon_schedule),
                      LrScheduler(lr_schedule),
                  ] + ([TradesScheduler(trades_schedule)] if trades_schedule else []),
    )

    print('model training done.')

    return g


def script(
        dataset,
        epsilon,
        epsilon_schedule='fixed',
        loss='crossentropy',
        augmentation='standard',
        epochs=100,
        batch_size=128,
        optimizer='adam',
        lr=1e-3,
        lr_schedule='fixed',
        trades_schedule=None,
        plot_learning_curve=False,
        INTERNAL_LAYER_SIZES=[64],
        input_size=28,
):
    g = train_gloro(
        dataset,
        epsilon,
        epsilon_schedule=epsilon_schedule,
        loss=loss,
        augmentation=augmentation,
        epochs=epochs,
        batch_size=batch_size,
        optimizer=optimizer,
        lr=lr,
        lr_schedule=lr_schedule,
        trades_schedule=trades_schedule,
        INTERNAL_LAYER_SIZES=INTERNAL_LAYER_SIZES,
        input_size=input_size
    )

    print('getting model accuracy numbers...')
    # Access the training accuracy
    final_training_accuracy = g.history.history['sparse_categorical_accuracy'][-1]

    # Access the validation accuracy (if validation_data was provided)
    final_validation_accuracy = g.history.history['val_sparse_categorical_accuracy'][-1]

    print(f'model training accuracy: {final_training_accuracy}; validation accuracy: {final_validation_accuracy}')

    print('extracting and saving model weights and biases...')
    # Extract weights and biases
    weights_and_biases = [
        (layer.get_weights()[0], layer.get_weights()[1])
        for layer in g.layers if len(layer.get_weights()) > 0]

    lipschitz_constants = [layer.lipschitz() for layer in g.layers if isinstance(layer, Dense)]

    # Create a directory to save the files if it does not exist
    save_dir = 'model_weights_csv'
    if not os.path.exists(save_dir):
        os.makedirs(save_dir)

    # Loop through each layer, extract weights and biases, and save them
    for i, (weights, biases) in enumerate(weights_and_biases):
        np.savetxt(os.path.join(save_dir, f'layer_{i}_weights.csv'), weights, delimiter=',', fmt='%f')
        np.savetxt(os.path.join(save_dir, f'layer_{i}_biases.csv'), biases, delimiter=',', fmt='%f')

    # Loop through each layer, extract weights and biases, and save them
    for i, c in enumerate(lipschitz_constants):
        np.savetxt(os.path.join(save_dir, f'layer_{i}_lipschitz.csv'), [c], delimiter=',', fmt='%f')

    print('model weights and biases extracted.')

    print("SUMMARY")
    print(f"lr_schedule: {lr_schedule}")
    print(f"epsilon: {epsilon}")
    print(f"dense layer sizes: {INTERNAL_LAYER_SIZES}")
    print(f"lipschitz constants: {lipschitz_constants}")

    # At the end of your script
    K.clear_session()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("dataset", type=str)
    parser.add_argument("epsilon", type=float)
    parser.add_argument("internal_layer_sizes", type=str)
    parser.add_argument("epochs", type=int)
    parser.add_argument("input_size", type=int)

    args = parser.parse_args()

    dataset = args.dataset
    epsilon = args.epsilon
    internal_layers = eval(args.internal_layer_sizes)
    epochs = args.epochs
    input_size = args.input_size

    print(f"Running with dataset: {dataset}")
    print(f"Running with internal layer dimensions: {internal_layers}")

    script(
        dataset=dataset,
        epsilon=epsilon,
        epsilon_schedule='fixed',
        batch_size=32,
        lr=1e-3,
        lr_schedule='decay_to_0.000001',
        epochs=epochs,
        loss='sparse_crossentropy',
        augmentation='none',
        INTERNAL_LAYER_SIZES=internal_layers,
        input_size=input_size)


if __name__ == "__main__":
    main()