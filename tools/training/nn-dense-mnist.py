import os
import csv
import json
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from sklearn.metrics import confusion_matrix

from gloro.training import losses
from gloro.training.callbacks import EpsilonScheduler, LrScheduler
from gloro.training.metrics import rejection_rate
from gloro.utils import print_if_verbose
from utils import get_data, get_optimizer
from gloro import GloroNet
from gloro.layers import Dense, Flatten, Input
import architectures

# Suppress TensorFlow info/warnings
os.environ['TF_CPP_MIN_LOG_LEVEL'] = '3'


# Helper: Ensure output directories exist
def ensure_directories(output_dir):
    dirs = {
        "csv": os.path.join(output_dir, "csv"),
        "models": os.path.join(output_dir, "models"),
        "analysis": os.path.join(output_dir, "analysis"),
    }
    for path in dirs.values():
        os.makedirs(path, exist_ok=True)
    return dirs


# Helper: Save CSV files
def save_csv(data, headers, filepath):
    with open(filepath, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(headers)
        writer.writerows(data)


# Helper: Save model metadata
def save_model_metadata(model, filepath, input_shape, hidden_nodes, num_classes, accuracy):
    metadata = {
        "input_nodes": input_shape,
        "hidden_nodes": hidden_nodes,
        "output_nodes": num_classes,
        "accuracy": accuracy,
        "optimizer": model.optimizer.get_config(),
        "layers": [
            {
                "name": layer.name,
                "weights_shape": layer.get_weights()[0].shape if layer.get_weights() else None,
                "biases_shape": layer.get_weights()[1].shape if layer.get_weights() else None,
            }
            for layer in model.layers
        ]
    }
    with open(filepath, "w") as f:
        json.dump(metadata, f, indent=4)


# Helper: Plot confusion matrix
def plot_confusion_matrix(y_true, y_pred, labels, save_path, title):
    matrix = confusion_matrix(y_true, y_pred)
    plt.figure(figsize=(10, 6))
    sns.heatmap(matrix, annot=True, fmt='d', cmap='Blues', xticklabels=labels, yticklabels=labels)
    plt.title(title)
    plt.xlabel("Predicted Label")
    plt.ylabel("True Label")
    plt.savefig(save_path)
    plt.close()


# Helper: Plot learning curves
def plot_learning_curves(history, save_path, title_suffix):
    plt.figure(figsize=(14, 7))
    # Accuracy
    plt.subplot(1, 2, 1)
    plt.plot(history['accuracy'], label='Training Accuracy', marker='o')
    plt.plot(history['val_accuracy'], label='Validation Accuracy', linestyle='--', marker='o')
    plt.title(f"Learning Curve: Accuracy ({title_suffix})")
    plt.xlabel("Epoch")
    plt.ylabel("Accuracy")
    plt.legend()

    # Loss
    plt.subplot(1, 2, 2)
    plt.plot(history['loss'], label='Training Loss', marker='o')
    plt.plot(history['val_loss'], label='Validation Loss', linestyle='--', marker='o')
    plt.title(f"Learning Curve: Loss ({title_suffix})")
    plt.xlabel("Epoch")
    plt.ylabel("Loss")
    plt.legend()

    plt.tight_layout()
    plt.savefig(save_path)
    plt.close()


# Train and compare gloro and keras models for MNIST
def compare_models(dataset, batch_size, augmentation, epsilon, epochs, lr, optimizer, loss, epsilon_schedule,
                   lr_schedule, verbose):
    # Set up directories
    output_dirs = ensure_directories("outputs")

    _print = print_if_verbose(verbose)

    # Load data
    _print('Loading data...')
    train, test, metadata = get_data(dataset, batch_size, augmentation)

    input_shape = metadata.features['image'].shape
    num_classes = metadata.features['label'].num_classes
    hidden_nodes = 200

    # Using layers from Gloro class
    x = Input(input_shape)
    z = Flatten()(x)
    z = Dense(hidden_nodes, kernel_initializer='glorot_uniform')(z)
    z = architectures.Activation('relu')(z)
    y = Dense(num_classes, kernel_initializer='glorot_uniform')(z)

    # ---- Gloro Model ----
    _print('Creating and training Gloro model...')
    g = GloroNet(x, y, epsilon)
    g.compile(
        loss=losses.get(loss),
        optimizer=get_optimizer(optimizer, lr),
        metrics=[rejection_rate],
    )
    g.fit(train, epochs=epochs, validation_data=test,
          callbacks=[EpsilonScheduler(epsilon_schedule), LrScheduler(lr_schedule)])

    # Evaluate Gloro model
    x_test, y_test = zip(*test.as_numpy_iterator())
    x_test = np.concatenate(x_test, axis=0)
    y_test = np.concatenate(y_test, axis=0)
    predictions_gloro = g.predict(x_test)
    gloro_accuracy = g.evaluate(test, verbose=0)[1]

    # Save Gloro predictions
    save_csv(
        [[i, int(y_test[i]), np.argmax(predictions_gloro[i]), predictions_gloro[i].tolist()] for i in
         range(len(y_test))],
        ["Index", "Correct Label", "Predicted Label", "Outputs"],
        os.path.join(output_dirs["csv"], "test_predictions_gloro.csv")
    )

    # ---- Keras Model ----
    # Keras Model Creation
    import keras
    from keras.losses import SparseCategoricalCrossentropy
    _print('creating Keras model...')
    # Define Keras model using the same architecture
    x_keras = Input(input_shape)
    z_keras = Flatten()(x_keras)  # Flatten the input for the dense layers
    z_keras = Dense(200, kernel_initializer='glorot_uniform')(z_keras)
    z_keras = architectures.Activation('relu')(z_keras)
    y_keras = Dense(num_classes, kernel_initializer='glorot_uniform')(z_keras)

    _print('Creating and training Keras model...')
    keras_model = keras.Model(inputs=x_keras, outputs=y_keras, name="keras_dense_model")
    keras_model.compile(
        optimizer=get_optimizer(optimizer, lr),
        loss=SparseCategoricalCrossentropy(from_logits=True),
        metrics=['accuracy']
    )
    history = keras_model.fit(train, epochs=epochs, validation_data=test, verbose=verbose)

    # Evaluate Keras model
    predictions_keras = keras_model.predict(x_test)
    keras_accuracy = keras_model.evaluate(x_test, y_test, verbose=0)[1]

    # Save Keras predictions
    save_csv(
        [[i, int(y_test[i]), np.argmax(predictions_keras[i]), predictions_keras[i].tolist()] for i in
         range(len(y_test))],
        ["Index", "Correct Label", "Predicted Label", "Outputs"],
        os.path.join(output_dirs["csv"], "test_predictions_keras.csv")
    )

    # ---- Analysis ----
    plot_confusion_matrix(y_test, np.argmax(predictions_gloro, axis=1), list(range(10)),
                          os.path.join(output_dirs["analysis"], "confusion_matrix_gloro.png"),
                          "Confusion Matrix for Gloro Model")

    plot_confusion_matrix(y_test, np.argmax(predictions_keras, axis=1), list(range(10)),
                          os.path.join(output_dirs["analysis"], "confusion_matrix_keras.png"),
                          "Confusion Matrix for Keras Model")

    plot_learning_curves(history.history, os.path.join(output_dirs["analysis"], "learning_curves_keras.png"),
                         "Keras Model")

    # Save metadata
    save_model_metadata(keras_model, os.path.join(output_dirs["models"], "keras_model_metadata.json"),
                        input_shape, hidden_nodes, num_classes, keras_accuracy)

    print("All outputs saved successfully.")


# Entry point
if __name__ == "__main__":
    compare_models(
        dataset='mnist',
        batch_size=512,
        augmentation='none',
        epsilon=1.58,
        epsilon_schedule='fixed',
        lr=1e-3,
        lr_schedule='fixed',
        optimizer='adam',
        loss="sparse_trades_kl_1.5",
        epochs=6,
        verbose=True,
    )