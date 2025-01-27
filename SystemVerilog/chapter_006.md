# Arrays

## Introduction
An array is a collection of variables of the same type, accessed using an index. SystemVerilog supports several types of arrays, including fixed-size arrays, dynamic arrays, associative arrays, and queues.

## Packed and Unpacked Arrays

### Packed Arrays
Packed arrays are contiguous sets of bits, which can be used to represent vectors or multi-dimensional arrays.
```SV
logic [7:0] packedArray;
initial begin
    packedArray = 8'b10101010;
    $display("packedArray = %b", packedArray);
end
```

### Unpacked Arrays
Unpacked arrays are collections of variables that are not necessarily contiguous in memory.
```SV
int unpackedArray[5];
initial begin
    unpackedArray[0] = 10;
    unpackedArray[1] = 20;
    unpackedArray[2] = 30;
    unpackedArray[3] = 40;
    unpackedArray[4] = 50;
    $display("unpackedArray[2] = %0d", unpackedArray[2]);
end
```

## Fixed-Size Arrays
A fixed-size array has a predefined number of elements.
```SV
int myArray[5];
initial begin
    myArray[0] = 10;
    myArray[1] = 20;
    myArray[2] = 30;
    myArray[3] = 40;
    myArray[4] = 50;
    $display("myArray[2] = %0d", myArray[2]);
end
```

### Methods

#### size()
The `size()` method returns the number of elements in the array.
```SV
int myArray[5] = '{1, 2, 3, 4, 5};
int size;
initial begin
    size = myArray.size();
    $display("Size: %0d", size);
end
```

## Dynamic Arrays
A dynamic array can change its size during runtime.
```SV
int myDynamicArray[];
initial begin
    myDynamicArray = new[5];
    myDynamicArray[0] = 10;
    myDynamicArray[1] = 20;
    myDynamicArray[2] = 30;
    myDynamicArray[3] = 40;
    myDynamicArray[4] = 50;
    $display("myDynamicArray[2] = %0d", myDynamicArray[2]);
end
```

### Methods

#### new()
The `new()` method allocates memory for the dynamic array.
```SV
int myDynamicArray[];
initial begin
    myDynamicArray = new[5];
    $display("Size after new: %0d", myDynamicArray.size());
end
```

#### size()
The `size()` method returns the number of elements in the dynamic array.
```SV
int myDynamicArray[];
initial begin
    myDynamicArray = new[5];
    $display("Size: %0d", myDynamicArray.size());
end
```

#### delete()
The `delete()` method removes all elements from the dynamic array.
```SV
int myDynamicArray[];
initial begin
    myDynamicArray = new[5];
    myDynamicArray.delete();
    $display("Size after delete: %0d", myDynamicArray.size());
end
```

## Associative Arrays
An associative array uses an index of any data type to access its elements.
```SV
int myAssocArray[string];
initial begin
    myAssocArray["one"] = 1;
    myAssocArray["two"] = 2;
    myAssocArray["three"] = 3;
    $display("myAssocArray['two'] = %0d", myAssocArray["two"]);
end
```

### Methods

#### num()
The `num()` method returns the number of elements in the associative array.
```SV
int myAssocArray[string];
initial begin
    myAssocArray["one"] = 1;
    myAssocArray["two"] = 2;
    $display("Number of elements: %0d", myAssocArray.num());
end
```

#### size()
The `size()` method returns the number of elements in the associative array.
```SV
int myAssocArray[string];
initial begin
    myAssocArray["one"] = 1;
    myAssocArray["two"] = 2;
    $display("Size: %0d", myAssocArray.size());
end
```

#### delete()
The `delete()` method removes all elements from the associative array.
```SV
int myAssocArray[string];
initial begin
    myAssocArray["one"] = 1;
    myAssocArray["two"] = 2;
    myAssocArray.delete();
    $display("Size after delete: %0d", myAssocArray.size());
end
```

#### delete(index)
The `delete(index)` method removes the element at the specified index from the associative array.
```SV
int myAssocArray[string];
initial begin
    myAssocArray["one"] = 1;
    myAssocArray["two"] = 2;
    myAssocArray.delete("one");
    $display("Size after deleting 'one': %0d", myAssocArray.size());
end
```

#### exists()
The `exists()` method checks if an element exists in the associative array.
```SV
int myAssocArray[string];
initial begin
    myAssocArray["one"] = 1;
    if (myAssocArray.exists("one")) begin
        $display("Element 'one' exists");
    end else begin
        $display("Element 'one' does not exist");
    end
end
```

#### first()
The `first()` method returns the first index in the associative array.
```SV
int myAssocArray[string];
string firstIndex;
initial begin
    myAssocArray["one"] = 1;
    myAssocArray.first(firstIndex);
    $display("First index: %s", firstIndex);
end
```

#### last()
The `last()` method returns the last index in the associative array.
```SV
int myAssocArray[string];
string lastIndex;
initial begin
    myAssocArray["one"] = 1;
    myAssocArray["two"] = 2;
    myAssocArray.last(lastIndex);
    $display("Last index: %s", lastIndex);
end
```

#### next()
The `next()` method returns the next index in the associative array.
```SV
int myAssocArray[string];
string currentIndex, nextIndex;
initial begin
    myAssocArray["one"] = 1;
    myAssocArray["two"] = 2;
    currentIndex = "one";
    myAssocArray.next(currentIndex, nextIndex);
    $display("Next index after 'one': %s", nextIndex);
end
```

#### prev()
The `prev()` method returns the previous index in the associative array.
```SV
int myAssocArray[string];
string currentIndex, prevIndex;
initial begin
    myAssocArray["one"] = 1;
    myAssocArray["two"] = 2;
    currentIndex = "two";
    myAssocArray.prev(currentIndex, prevIndex);
    $display("Previous index before 'two': %s", prevIndex);
end
```

## Queues
A queue is a variable-size, ordered collection of elements.
```SV
int myQueue[$];
initial begin
    myQueue.push_back(10);
    myQueue.push_back(20);
    myQueue.push_back(30);
    $display("myQueue[1] = %0d", myQueue[1]);
end
```

### Methods

#### size()
The `size()` method returns the number of elements in the queue.
```SV
int myQueue[$];
initial begin
    myQueue.push_back(10);
    myQueue.push_back(20);
    $display("Queue size: %0d", myQueue.size());
end
```

#### delete()
The `delete()` method removes all elements from the queue.
```SV
int myQueue[$];
initial begin
    myQueue.push_back(10);
    myQueue.push_back(20);
    myQueue.delete();
    $display("Queue size after delete: %0d", myQueue.size());
end
```

#### delete(index)
The `delete(index)` method removes the element at the specified index from the queue.
```SV
int myQueue[$];
initial begin
    myQueue.push_back(10);
    myQueue.push_back(20);
    myQueue.delete(0);
    $display("Queue size after deleting index 0: %0d", myQueue.size());
end
```

#### insert()
The `insert()` method inserts an element at a specified position in the queue.
```SV
int myQueue[$];
initial begin
    myQueue.push_back(10);
    myQueue.push_back(20);
    myQueue.insert(1, 15);
    $display("Element at position 1: %0d", myQueue[1]);
end
```

#### pop_front()
The `pop_front()` method removes and returns the first element of the queue.
```SV
int myQueue[$];
int firstElement;
initial begin
    myQueue.push_back(10);
    myQueue.push_back(20);
    firstElement = myQueue.pop_front();
    $display("First element: %0d", firstElement);
end
```

#### pop_back()
The `pop_back()` method removes and returns the last element of the queue.
```SV
int myQueue[$];
int lastElement;
initial begin
    myQueue.push_back(10);
    myQueue.push_back(20);
    lastElement = myQueue.pop_back();
    $display("Last element: %0d", lastElement);
end
```

#### push_front()
The `push_front()` method adds an element to the front of the queue.
```SV
int myQueue[$];
initial begin
    myQueue.push_front(10);
    myQueue.push_front(20);
    $display("First element: %0d", myQueue[0]);
end
```

#### push_back()
The `push_back()` method adds an element to the end of the queue.
```SV
int myQueue[$];
initial begin
    myQueue.push_back(10);
    myQueue.push_back(20);
    $display("Last element: %0d", myQueue[$-1]);
end
```

## Exercise
1. Create a packed array and an unpacked array, initialize them with some values, and display the values using `$display`.
2. Create a fixed-size array and initialize it with some values.
3. Create a dynamic array, allocate memory, and initialize it with some values.
4. Create an associative array with string keys and integer values, and initialize it with some values.
5. Create a queue, add some elements using `push_back()`, and remove the last element using `pop_back()`.
6. Display the size of each array using the `size()` method.
7. Delete a specific index from an associative array and a queue, and display the size after deletion.
