# Chapter 4: Array

## Introduction
Arrays in SystemVerilog are used to store collections of data elements. They can be packed or unpacked, fixed-size, dynamic, associative, or queues.

## Packed and Unpacked Arrays
### Packed Array
A packed array is a contiguous set of bits.

```systemverilog
logic [7:0] packed_array;
```

### Unpacked Array
An unpacked array is an array of elements.

```systemverilog
int unpacked_array [0:3];
```

## Fixed Size Array
A fixed-size array has a predefined number of elements.

```systemverilog
int fixed_array [0:9];
```

### Methods for Fixed Size Arrays
| Method | Description | Example |
|--------|-------------|---------|
| `size` | Returns the number of elements in the array | `int size = fixed_array.size();` |

## Dynamic Array
A dynamic array can change its size during runtime.

```systemverilog
int dynamic_array [];
initial begin
  dynamic_array = new[10]; // Allocate 10 elements
end
```

### Methods for Dynamic Arrays
| Method | Description | Example |
|--------|-------------|---------|
| `size` | Returns the number of elements in the array | `int size = dynamic_array.size();` |
| `new` | Allocates memory for the array | `dynamic_array = new[10];` |
| `delete` | Deallocates memory for the array | `dynamic_array.delete();` |

## Associative Array
An associative array uses an index of any data type to access its elements.

```systemverilog
int associative_array [string];
initial begin
  associative_array["key1"] = 1;
  associative_array["key2"] = 2;
end
```

### Methods for Associative Arrays
| Method | Description | Example |
|--------|-------------|---------|
| `num` | Returns the number of elements in the array | `int num = associative_array.num();` |
| `size` | Returns the number of elements in the array | `int size = associative_array.size();` |
| `delete` | Deletes all elements in the array | `associative_array.delete();` |
| `delete index` | Deletes the element at the specified index | `associative_array.delete("key1");` |
| `exists` | Checks if an element exists at the specified index | `if (associative_array.exists("key1")) ...` |
| `first` | Returns the first index in the array | `string first_index; associative_array.first(first_index);` |
| `last` | Returns the last index in the array | `string last_index; associative_array.last(last_index);` |
| `next` | Returns the next index in the array | `string next_index; associative_array.next(next_index);` |
| `prev` | Returns the previous index in the array | `string prev_index; associative_array.prev(prev_index);` |

## Queue
A queue is a variable-size, ordered collection of elements.

```systemverilog
int queue [$];
initial begin
  queue.push_back(1);
  queue.push_back(2);
end
```

### Methods for Queues
| Method | Description | Example |
|--------|-------------|---------|
| `size` | Returns the number of elements in the queue | `int size = queue.size();` |
| `insert` | Inserts an element at the specified position | `queue.insert(1, 5);` |
| `delete` | Deletes all elements in the queue | `queue.delete();` |
| `delete index` | Deletes the element at the specified index | `queue.delete(4);` |
| `pop_front` | Removes the first element in the queue | `queue.pop_front();` |
| `pop_back` | Removes the last element in the queue | `queue.pop_back();` |
| `push_front` | Adds an element to the front of the queue | `queue.push_front(0);` |
| `push_back` | Adds an element to the end of the queue | `queue.push_back(3);` |

## Exercises
1. Declare a packed array and initialize it with a value.
2. Create an unpacked array and iterate over its elements.
3. Define a fixed-size array and assign values to its elements.
4. Create a dynamic array and allocate memory for it.
5. Use an associative array to store key-value pairs.
6. Implement a queue and perform push and pop operations.

## Conclusion
Arrays in SystemVerilog provide a flexible way to store and manipulate collections of data. Understanding the different types of arrays and their use cases is essential for efficient hardware modeling and simulation.
