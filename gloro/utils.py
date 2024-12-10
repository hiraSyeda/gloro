import numpy as np
import tensorflow as tf

from tensorflow.python.framework import ops

import gloro


def add_extra_column(y):
    if isinstance(y, np.ndarray):
        return add_extra_column_np(y)
    else:
        return add_extra_column_tf(y)

def add_extra_column_tf(y):
    return tf.concat((y, tf.zeros((tf.shape(y)[0], 1))), axis=1)

def add_extra_column_np(y):
    return np.concatenate((y, np.zeros((y.shape[0], 1))), axis=1)


def set_value(x, value):
    # Safely handle dtype
    dtype = getattr(x.dtype, 'base_dtype', x.dtype) if hasattr(x.dtype, 'base_dtype') else x.dtype
    value = np.asarray(value, dtype=dtype.name if hasattr(dtype, 'name') else dtype)
    x.assign(value)  # Ensure the value is correctly assigned to the tf.Variable

def batch_set_value(tuples):
    with ops.init_scope():
        for x, value in tuples:
            x.assign(np.asarray(value, dtype=x.dtype.base_dtype.name))


def get_value(x):
    return x.numpy()


def l2_normalize(x, axis=None):
    return x / (
        tf.sqrt(tf.reduce_sum(x**2., axis=axis, keepdims=True)) +
            gloro.constants.EPS)


def print_if_verbose(verbose):
    if verbose:
        return lambda s: print(s)

    else:
        return lambda s: None
