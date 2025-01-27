# Array Manipulation

SystemVerilog provides several built-in methods to manipulate arrays. These methods can be used to perform operations such as searching, sorting, and reducing arrays.

## Array Reduction Methods

### and()
The `and()` method performs a bitwise AND reduction on all elements of the array.
```systemverilog
int myArray[4] = '{1, 1, 1, 1};
int result;
initial begin
    result = myArray.and();
    $display("AND reduction: %0d", result);
end
```

### or()
The `or()` method performs a bitwise OR reduction on all elements of the array.
```systemverilog
int myArray[4] = '{1, 0, 1, 0};
int result;
initial begin
    result = myArray.or();
    $display("OR reduction: %0d", result);
end
```

### xor()
The `xor()` method performs a bitwise XOR reduction on all elements of the array.
```systemverilog
int myArray[4] = '{1, 0, 1, 0};
int result;
initial begin
    result = myArray.xor();
    $display("XOR reduction: %0d", result);
end
```

## Array Ordering Methods

### reverse()
The `reverse()` method reverses the order of elements in the array.
```systemverilog
int myArray[4] = '{1, 2, 3, 4};
initial begin
    myArray.reverse();
    $display("Reversed array: %p", myArray);
end
```

### sort()
The `sort()` method sorts the elements of the array in ascending order.
```systemverilog
int myArray[4] = '{4, 3, 2, 1};
initial begin
    myArray.sort();
    $display("Sorted array: %p", myArray);
end
```

### rsort()
The `rsort()` method sorts the elements of the array in descending order.
```systemverilog
int myArray[4] = '{1, 2, 3, 4};
initial begin
    myArray.rsort();
    $display("Reverse sorted array: %p", myArray);
end
```

## Array Searching Methods

### find()
The `find()` method returns the indices of elements that match a given condition.
```systemverilog
int myArray[4] = '{1, 2, 3, 4};
int indices[];
initial begin
    indices = myArray.find(x) with (x > 2);
    $display("Indices of elements > 2: %p", indices);
end
```

### find_index()
The `find_index()` method returns the index of the first element that matches a given condition.
```systemverilog
int myArray[4] = '{1, 2, 3, 4};
int index;
initial begin
    index = myArray.find_index(x) with (x > 2);
    $display("Index of first element > 2: %0d", index);
end
```

### find_first()
The `find_first()` method returns the first element that matches a given condition.
```systemverilog
int myArray[4] = '{1, 2, 3, 4};
int element;
initial begin
    element = myArray.find_first(x) with (x > 2);
    $display("First element > 2: %0d", element);
end
```

### find_last()
The `find_last()` method returns the last element that matches a given condition.
```systemverilog
int myArray[4] = '{1, 2, 3, 4};
int element;
initial begin
    element = myArray.find_last(x) with (x > 2);
    $display("Last element > 2: %0d", element);
end
```

## Array Uniqueness Methods

### unique()
The `unique()` method returns the unique elements of the array.
```systemverilog
int myArray[4] = '{1, 2, 2, 3};
int uniqueArray[];
initial begin
    uniqueArray = myArray.unique();
    $display("Unique elements: %p", uniqueArray);
end
```

## Array Sum Methods

### sum()
The `sum()` method returns the sum of all elements in the array.
```systemverilog
int myArray[4] = '{1, 2, 3, 4};
int result;
initial begin
    result = myArray.sum();
    $display("Sum of elements: %0d", result);
end
```

## Exercise
1. Create an array and perform a bitwise AND reduction using the `and()` method.
2. Reverse the order of elements in an array using the `reverse()` method.
3. Sort an array in ascending order using the `sort()` method.
4. Find the indices of elements greater than a given value using the `find()` method.
5. Return the unique elements of an array using the `unique()` method.
6. Calculate the sum of all elements in an array using the `sum()` method.
