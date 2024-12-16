import os
import csv
import json
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
from sklearn.metrics import confusion_matrix
from utils import get_data
from train_gloro import train_gloro

# Ensure TensorFlow logging suppression and GPU memory growth
os.environ['TF_CPP_MIN_LOG_LEVEL'] = '3'  # Suppress TensorFlow info/warnings


def train_custom_dense_model():
    print("Starting training for custom_dense model...")

    model = train_gloro(
        dataset="mnist",
        architecture="custom_dense",
        epsilon=1.58,
        epsilon_schedule='[0.01]-log-[50%:1.1]',
        epochs=6,
        batch_size=512,
        loss="sparse_trades_kl_1.5",
        augmentation="none",
        optimizer="adam",
        lr=1e-3,
        lr_schedule="fixed",
        power_iterations=5,  # Placeholder argument, if unused
        trades_schedule=None,
        verbose=True,
    )
    print("Training complete.")

    # Load test data
    print("Loading MNIST dataset for evaluation...")
    _, test, _ = get_data("mnist", 512, "none")

    # Convert test dataset to NumPy arrays
    def dataset_to_numpy(dataset):
        x, y = zip(*dataset.as_numpy_iterator())
        return np.concatenate(x, axis=0), np.concatenate(y, axis=0)

    x_test, y_test = dataset_to_numpy(test)

    print("Evaluating model...")
    test_loss, test_rejection_rate = model.evaluate(test, verbose=0)
    predictions = model.predict(x_test)

    # Set up output directories
    OUTPUT_DIR = "outputs_gloro_custom"
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    CSV_DIR = os.path.join(OUTPUT_DIR, "csv")
    ANALYSIS_DIR = os.path.join(OUTPUT_DIR, "analysis")
    os.makedirs(CSV_DIR, exist_ok=True)
    os.makedirs(ANALYSIS_DIR, exist_ok=True)

    # Save predictions to CSV
    print("Saving predictions to CSV...")
    predictions_csv = [
        [i, int(y_test[i]), np.argmax(predictions[i]), predictions[i].tolist()]
        for i in range(len(predictions))
    ]
    with open(os.path.join(CSV_DIR, "test_predictions.csv"), "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["Index", "True Label", "Predicted Label", "Outputs"])
        writer.writerows(predictions_csv)

    # Save model metadata
    print("Saving model metadata...")
    metadata = {
        "architecture": "custom_dense",
        "epsilon": 1.58,
        "epochs": 6,
        "batch_size": 512,
        "test_loss": test_loss,
        "test_rejection_rate": test_rejection_rate,
    }
    with open(os.path.join(OUTPUT_DIR, "model_metadata.json"), "w") as f:
        json.dump(metadata, f, indent=4)

    # Generate Confusion Matrix
    print("Generating confusion matrix...")
    true_labels = y_test.astype(int)  # Ensure labels are integers
    predicted_labels = np.argmax(predictions, axis=1)
    conf_matrix = confusion_matrix(true_labels, predicted_labels)

    plt.figure(figsize=(10, 6))
    sns.heatmap(conf_matrix, annot=True, fmt='d', cmap='Blues', xticklabels=range(10), yticklabels=range(10))
    plt.title("Confusion Matrix: Custom Gloro Dense Model")
    plt.xlabel("Predicted Label")
    plt.ylabel("True Label")
    plt.savefig(os.path.join(ANALYSIS_DIR, "confusion_matrix.png"))
    plt.close()

    print("Evaluation and analysis complete. Outputs saved successfully.")

if __name__ == "__main__":
    train_custom_dense_model()
