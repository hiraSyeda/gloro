import numpy as np
import tensorflow as tf


def mprint(string):
    print(string, end="")

def printlist(floatlist):
    print(",".join(f"{num:.5f}" for num in floatlist))

def format_weights(weights):
    weightslen = len(weights)
    for w, mat in enumerate(weights):
        mprint("[")
        for r, row in enumerate(mat):
            mprint("[")
            mprint(",".join(f"{num:.5f}" for num in row))
            mprint("]")
            if r < len(mat) - 1:
                mprint(",")
        mprint("]")
        if w < weightslen - 1:
            mprint(",")

# Utils before running the certifier, i.e. for training the gloro model
def resize_image(input_size):
    def resize_fn(image, label):
        image = tf.image.resize(image, [input_size, input_size])
        return image, label
    return resize_fn

def build_model(Input, Flatten, Dense, input_size=28, internal_layer_sizes=[], channels=1):
    """set input_size to something smaller if the model is downsampled"""
    inputs = Input((input_size, input_size, channels))
    z = Flatten()(inputs)
    for size in internal_layer_sizes:
        z = Dense(size, activation='relu')(z)
    outputs = Dense(10)(z)
    return (inputs, outputs)

# Utils for running the certifier, i.e. once the gloro model has been trained
def load_and_set_weights(csv_loc, internal_layer_sizes, model):
    """model should already be built. This will compile it too"""
    dense_weights = []
    dense_biases = []
    dense_zero_biases = []
    i=0
    # always one extra iteration than internal_layer_sizes length
    while i<=len(internal_layer_sizes):
        dense_weights.append(np.loadtxt(csv_loc+f"layer_{i}_weights.csv", delimiter=","))
        dense_biases.append(np.loadtxt(csv_loc+f"layer_{i}_biases.csv", delimiter=","))
        dense_zero_biases.append(np.zeros_like(dense_biases[i]))

        model.layers[i+2].set_weights([dense_weights[i], dense_zero_biases[i]])
        i=i+1

    model.compile(optimizer='adam',
                  loss=tf.keras.losses.CategoricalCrossentropy(from_logits=True),
                  metrics=['accuracy'])

    
def load_mnist_test_data(input_size=28):
    """set input_size to resize the test dataset. Returns a pair (x_test, y_test)"""
    # turn off SSL cert checking :(
    import ssl
    ssl._create_default_https_context = ssl._create_unverified_context
    (x_train, y_train), (x_test, y_test) = tf.keras.datasets.mnist.load_data()

    # Normalize pixel values to [0, 1]
    x_test = x_test.astype('float32') / 255.0
    if input_size != 28:
        resized_tensor = tf.image.resize(x_test[..., tf.newaxis], [input_size, input_size])
        if tf.executing_eagerly():
            x_test=resized_tensor.numpy()
        else:
            # Convert the tensor to NumPy using a session
            with tf.compat.v1.Session() as sess:
                x_test = sess.run(resized_tensor)
                x_test = np.squeeze(x_test, axis=-1)  # Remove the last dimension

    # Convert labels to one-hot encoded format
    y_test = tf.keras.utils.to_categorical(y_test, num_classes=10)

    return (x_test, y_test)
