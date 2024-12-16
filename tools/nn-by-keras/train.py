import csv
import os
import json
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from sklearn.metrics import confusion_matrix
import keras
from keras import layers
from keras import datasets as ds

"""
train.py

This script trains a fully connected (Dense) neural network with 2 layers on the MNIST dataset.
The network is designed as follows:
    - Input Layer: 784 nodes (28x28 flattened grayscale images)
    - Hidden Layer: 200 nodes with ReLU activation
    - Output Layer: 10 nodes with Softmax activation (for 10 classes: digits 0-9)

Model Features:
    - Optimizer: Adam (adaptive learning rate)
    - Loss Function: Categorical Crossentropy (for multi-class classification)
    - Metrics: Accuracy

Outputs:
    - Model saved in `.keras` format for reuse.
    - Metadata (JSON): Input, hidden, and output layer details, optimizer configuration, and accuracy.
    - Predictions (CSV): Test set predictions, including the correct label, predicted label, and probabilities.
    - Weights and Biases (CSV): Layer weights and biases for reproducibility and analysis.
"""

# Define key parameters for the neural network
INPUT_NODES = 784
HIDDEN_NODES = 200
OUTPUT_NODES = 10
EPOCHS = 10
BATCH_SIZE = 32

output_dir = "outputs"
csv_dir = os.path.join(output_dir, "csv")
models_dir = os.path.join(output_dir, "models")
analysis_dir = os.path.join(output_dir, "analysis")

# Explicitly create directories
if not os.path.exists(csv_dir):
    os.makedirs(csv_dir)
if not os.path.exists(models_dir):
    os.makedirs(models_dir)
if not os.path.exists(analysis_dir):
    os.makedirs(analysis_dir)

# Step 1: Load and Preprocess the Data
(x_train, y_train), (x_test, y_test) = ds.mnist.load_data()

# Flatten 28x28 images into 784-dimensional vectors and normalize
x_train = x_train.reshape(-1, INPUT_NODES).astype('float32') / 255.0
x_test = x_test.reshape(-1, INPUT_NODES).astype('float32') / 255.0

# Convert labels to one-hot encoding
y_train = keras.utils.to_categorical(y_train, OUTPUT_NODES)
y_test = keras.utils.to_categorical(y_test, OUTPUT_NODES)

# Step 2: Define the Model
model = keras.Sequential([
    layers.Input(shape=(INPUT_NODES,)),
    layers.Dense(HIDDEN_NODES, activation='relu'),
    layers.Dense(OUTPUT_NODES, activation='softmax')
])

# Step 3: Compile the Model
model.compile(
    optimizer='adam',
    loss='categorical_crossentropy',
    metrics=['accuracy']
)

# Step 4: Train the Model
history = model.fit(  # Capture the training history
    x_train, y_train,
    validation_data=(x_test, y_test),
    epochs=EPOCHS,
    batch_size=BATCH_SIZE,
    verbose=1
)

# Evaluate and save model performance
loss, accuracy = model.evaluate(x_test, y_test, verbose=0)

# Save predictions
predictions = model.predict(x_test)
predictions_csv = [
    [i, np.argmax(y_test[i]), np.argmax(predictions[i]), predictions[i].tolist()]
    for i in range(len(predictions))
]
# Save to CSV
with open(os.path.join(csv_dir, "test_predictions.csv"), "w", newline="") as f:
    writer = csv.writer(f)
    writer.writerow(["Index", "Correct Label", "Predicted Label", "Outputs"])
    writer.writerows(predictions_csv)

# Save weights and biases
weights_csv = [
    ["Layer", "Weights"],
    ["Input-to-Hidden"] + model.layers[0].get_weights()[0].tolist(),
    ["Hidden-to-Output"] + model.layers[1].get_weights()[0].tolist()
]
biases_csv = [
    ["Layer", "Biases"],
    ["Input-to-Hidden Biases"] + model.layers[0].get_weights()[1].tolist(),
    ["Hidden-to-Output Biases"] + model.layers[1].get_weights()[1].tolist()
]

# Save weights and biases to CSV
with open(os.path.join(csv_dir, "weights.csv"), "w", newline="") as f:
    writer = csv.writer(f)
    writer.writerows(weights_csv)

with open(os.path.join(csv_dir, "biases.csv"), "w", newline="") as f:
    writer = csv.writer(f)
    writer.writerows(biases_csv)

# Save model metadata
metadata = {
    "input_nodes": INPUT_NODES,
    "hidden_nodes": HIDDEN_NODES,
    "output_nodes": OUTPUT_NODES,
    "accuracy": accuracy,
    "optimizer": model.optimizer.get_config(),
    "layers": [
        {
            "name": layer.name,
            "weights_shape": layer.get_weights()[0].shape if layer.get_weights() else None,
            "biases_shape": layer.get_weights()[1].shape if layer.get_weights() else None
        }
        for layer in model.layers
    ]
}
with open(os.path.join(models_dir, "model_metadata.json"), "w") as f:
    json.dump(metadata, f, indent=4)

# Save the model
model.save(os.path.join(models_dir, "mnist_nn_model.keras"))

# Save test results
test_results = {
    "performance": accuracy,
    "predictions": [
        {
            "correct_label": int(np.argmax(y_test[i])),
            "predicted_label": int(np.argmax(predictions[i])),
            "outputs": predictions[i].tolist()
        } for i in range(10)  # Save only the first 10 predictions
    ]
}
with open(os.path.join(models_dir, "test_results.json"), "w") as f:
    json.dump(test_results, f, indent=4)

# Generate Confusion Matrix
true_labels = np.argmax(y_test, axis=1)
predicted_labels = np.argmax(predictions, axis=1)
conf_matrix = confusion_matrix(true_labels, predicted_labels)

plt.figure(figsize=(10, 6))
sns.heatmap(conf_matrix, annot=True, fmt='d', cmap='Blues', xticklabels=list(range(10)), yticklabels=list(range(10)))
plt.title(
    "Confusion Matrix\n\nA table comparing the model's predictions to actual labels.\nDiagonal cells: "
    "Correct predictions.\nOff-diagonal cells: Misclassifications.",
    loc='left')
plt.xlabel("Predicted Label")
plt.ylabel("True Label")
conf_matrix_path = os.path.join(analysis_dir, "confusion_matrix.png")
plt.savefig(conf_matrix_path)
plt.close()

# Generate Learning Curves
plt.figure(figsize=(14, 7))

# Accuracy Curve
plt.subplot(1, 2, 1)
plt.plot(history.history['accuracy'], label='Training Accuracy', marker='o')
plt.plot(history.history['val_accuracy'], label='Validation Accuracy', linestyle='--', marker='o')
plt.title(
    "Learning Curve: Accuracy\n\nShows how accuracy changes during training and validation.\n"
    "Helps identify overfitting (training >> validation accuracy).",
    loc='left')
plt.xlabel("Epoch")
plt.ylabel("Accuracy")
plt.legend()

# Loss Curve
plt.subplot(1, 2, 2)
plt.plot(history.history['loss'], label='Training Loss', marker='o')
plt.plot(history.history['val_loss'], label='Validation Loss', linestyle='--', marker='o')
plt.title(
    "Learning Curve: Loss\n\nDisplays the model's loss values during training and validation.\n"
    "Helps diagnose underfitting or overfitting issues.",
    loc='left')
plt.xlabel("Epoch")
plt.ylabel("Loss")
plt.legend()

# Save the learning curve
learning_curve_path = os.path.join(analysis_dir, "learning_curves.png")
plt.tight_layout()
plt.savefig(learning_curve_path)
plt.close()

print(f"Confusion matrix saved at {conf_matrix_path}")
print(f"Learning curves saved at {learning_curve_path}")

print("All outputs saved successfully.")
