import os
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

    # Evaluate the model.
    train, test, metadata = get_data("mnist", 512, "none")

    train_eval = model.evaluate(train)
    test_eval = model.evaluate(test)

    results = {}

    results.update({
        'test_' + metric.name.split('pred_')[-1]: round(value, 4)
        for metric, value in zip(model.metrics, test_eval)
    })
    results.update({
        'train_' + metric.name.split('pred_')[-1]: round(value, 4)
        for metric, value in zip(model.metrics, train_eval)
    })

    print(results)

    return results

if __name__ == "__main__":
    train_custom_dense_model()
