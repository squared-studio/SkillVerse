# Basic System Tasks

SystemVerilog provides several system tasks for various purposes such as displaying messages, controlling simulation, and file operations. Here are some basic system tasks with examples and explanations:

## $display
The `$display` task is used to print messages to the console.
```SV
module display_example;
    initial begin
        $display("Hello, SystemVerilog!");
    end
endmodule
```
This example prints "Hello, SystemVerilog!" to the console.

## $monitor
The `$monitor` task continuously monitors and prints the values of variables whenever they change.
```SV
module monitor_example;
    reg [3:0] a, b;
    initial begin
        $monitor("At time %0t: a = %0d, b = %0d", $time, a, b);
        a = 4'b0001;
        b = 4'b0010;
        #10 a = 4'b0100;
        #10 b = 4'b1000;
    end
endmodule
```
This example prints the values of `a` and `b` whenever they change.

## $time
The `$time` task returns the current simulation time.
```SV
module time_example;
    initial begin
        #5 $display("Current time: %0t", $time);
    end
endmodule
```
This example prints the current simulation time after 5 time units.

## $finish
The `$finish` task terminates the simulation.
```SV
module finish_example;
    initial begin
        $display("Simulation will finish now.");
        $finish;
    end
endmodule
```
This example prints a message and then ends the simulation.

## $stop
The `$stop` task pauses the simulation and allows for interactive debugging.
```SV
module stop_example;
    initial begin
        $display("Simulation will stop now.");
        $stop;
    end
endmodule
```
This example prints a message and then pauses the simulation.

## $random
The `$random` task generates random numbers.
```SV
module random_example;
    initial begin
        $display("Random number: %0d", $random);
    end
endmodule
```
This example prints a random number to the console.

## $dumpfile
The `$dumpfile` task specifies the name of the dump file to store simulation waveforms.
```SV
module dumpfile_example;
    initial begin
        $dumpfile("waveform.vcd");
    end
endmodule
```
This example specifies "waveform.vcd" as the dump file to store simulation waveforms.

## $dumpvars
The `$dumpvars` task dumps the values of variables to the dump file for waveform viewing.
```SV
module dumpvars_example;
    reg [3:0] a, b;
    initial begin
        $dumpfile("waveform.vcd");
        $dumpvars(0, dumpvars_example);
        a = 4'b0001;
        b = 4'b0010;
        #10 a = 4'b0100;
        #10 b = 4'b1000;
    end
endmodule
```
This example dumps the values of variables `a` and `b` to "waveform.vcd" for waveform viewing.