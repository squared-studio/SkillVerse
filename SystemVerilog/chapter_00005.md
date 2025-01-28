# Array Manipulation

## Introduction
SystemVerilog provides several built-in methods for manipulating arrays. These methods can be used to perform various operations on arrays, such as finding elements, sorting, reversing, and more.

## Methods for Array Manipulation
| Method | Description | Example |
|--------|-------------|---------|
| `find()` | Returns all elements satisfying the given expression | `int found[] = array.find(x > 5);` |
| `find_index()` | Returns the indices of all elements satisfying the given expression | `int indices[] = array.find_index(x > 5);` |
| `find_first()` | Returns the first element satisfying the given expression | `int first = array.find_first(x > 5);` |
| `find_first_index()` | Returns the index of the first element satisfying the given expression | `int first_index = array.find_first_index(x > 5);` |
| `find_last()` | Returns the last element satisfying the given expression | `int last = array.find_last(x > 5);` |
| `find_last_index()` | Returns the index of the last element satisfying the given expression | `int last_index = array.find_last_index(x > 5);` |
| `min()` | Returns the element with minimum value or whose expression evaluates to a minimum | `int min_val = array.min();` |
| `max()` | Returns the element with maximum value or whose expression evaluates to a maximum | `int max_val = array.max();` |
| `unique()` | Returns all elements with unique values or whose expression evaluates to a unique value | `int unique_vals[] = array.unique();` |
| `unique_index()` | Returns the indices of all elements with unique values or whose expression evaluates to a unique value | `int unique_indices[] = array.unique_index();` |
| `reverse()` | Reverses the order of elements in the array | `array.reverse();` |
| `sort()` | Sorts the array in ascending order, optionally using with clause | `array.sort();` |
| `rsort()` | Sorts the array in descending order, optionally using with clause | `array.rsort();` |
| `shuffle()` | Randomizes the order of the elements in the array. with clause is not allowed here. | `array.shuffle();` |
| `sum()` | Returns the sum of all array elements | `int total = array.sum();` |
| `product()` | Returns the product of all array elements | `int prod = array.product();` |
| `and()` | Returns the bitwise AND (&) of all array elements | `int and_result = array.and();` |
| `or()` | Returns the bitwise OR (\|) of all array elements | `int or_result = array.or();` |
| `xor()` | Returns the bitwise XOR (^) of all array elements | `int xor_result = array.xor();` |

## Examples
### `find()`
```SV
int array[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
int found[] = array.find(x > 5);
```

### `find_index()`
```SV
int array[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
int indices[] = array.find_index(x > 5);
```

### `find_first()`
```SV
int array[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
int first = array.find_first(x > 5);
```

### `find_first_index()`
```SV
int array[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
int first_index = array.find_first_index(x > 5);
```

### `find_last()`
```SV
int array[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
int last = array.find_last(x > 5);
```

### `find_last_index()`
```SV
int array[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
int last_index = array.find_last_index(x > 5);
```

### `min()`
```SV
int array[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
int min_val = array.min();
```

### `max()`
```SV
int array[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
int max_val = array.max();
```

### `unique()`
```SV
int array[] = {1, 2, 2, 3, 4, 4, 5};
int unique_vals[] = array.unique();
```

### `unique_index()`
```SV
int array[] = {1, 2, 2, 3, 4, 4, 5};
int unique_indices[] = array.unique_index();
```

### `reverse()`
```SV
int array[] = {1, 2, 3, 4, 5};
array.reverse();
```

### `sort()`
```SV
int array[] = {5, 3, 1, 4, 2};
array.sort();
```

### `rsort()`
```SV
int array[] = {5, 3, 1, 4, 2};
array.rsort();
```

### `shuffle()`
```SV
int array[] = {1, 2, 3, 4, 5};
array.shuffle();
```

### `sum()`
```SV
int array[] = {1, 2, 3, 4, 5};
int total = array.sum();
```

### `product()`
```SV
int array[] = {1, 2, 3, 4, 5};
int prod = array.product();
```

### `and()`
```SV
int array[] = {1, 2, 3, 4, 5};
int and_result = array.and();
```

### `or()`
```SV
int array[] = {1, 2, 3, 4, 5};
int or_result = array.or();
```

### `xor()`
```SV
int array[] = {1, 2, 3, 4, 5};
int xor_result = array.xor();
```

## Exercises
1. Use the `find()` method to find all elements greater than 5 in an array.
2. Use the `sort()` method to sort an array in ascending order.
3. Use the `reverse()` method to reverse the order of elements in an array.
4. Use the `sum()` method to find the sum of all elements in an array.
5. Use the `unique()` method to find all unique elements in an array.

## Conclusion
Array manipulation methods in SystemVerilog provide powerful tools for working with arrays. Understanding these methods is essential for efficient hardware modeling and simulation.
