# string
A `string` is a dynamic array of characters used to store text. SystemVerilog provides several methods to manipulate strings.

## Declaring and Initializing Strings
```systemverilog
string myString;
initial begin
    myString = "Hello, SystemVerilog!";
    $display("%s", myString);
end
```

## String Methods

### len()
The `len()` method returns the length of the string.
```systemverilog
string myString = "Hello";
int length;
initial begin
    length = myString.len();
    $display("Length: %0d", length);
end
```

### tolower()
The `tolower()` method converts all characters in the string to lowercase.
```systemverilog
string myString = "HELLO";
initial begin
    myString = myString.tolower();
    $display("%s", myString);
end
```

### toupper()
The `toupper()` method converts all characters in the string to uppercase.
```systemverilog
string myString = "hello";
initial begin
    myString = myString.toupper();
    $display("%s", myString);
end
```

### substr()
The `substr()` method extracts a substring from the string.
```systemverilog
string myString = "Hello, SystemVerilog!";
string subString;
initial begin
    subString = myString.substr(7, 10);
    $display("%s", subString);
end
```

## Exercise
1. Create a string variable and initialize it with a sentence.
2. Use the `len()` method to find the length of the string.
3. Convert the string to uppercase using the `toupper()` method.
4. Extract a substring from the string using the `substr()` method.
5. Display all the results using `$display`.
