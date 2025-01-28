# Built-in System Tasks and System Functions

## Display Tasks
SystemVerilog provides several tasks for displaying information during simulation.

### `$display`
Displays information at the time of execution.

```SV
module display_example;
  initial begin
    $display("Hello, SystemVerilog!");
  end
endmodule
```

### `$monitor`
Continuously monitors and displays information whenever a specified variable changes.

```SV
module monitor_example;
  reg [3:0] a;
  initial begin
    $monitor("At time %0t, a = %0d", $time, a);
    a = 4'b0000;
    #5 a = 4'b0101;
    #5 a = 4'b1111;
  end
endmodule
```

### `$strobe`
Displays information at the end of the current simulation time step.

```SV
module strobe_example;
  initial begin
    $strobe("End of time step: %0t", $time);
  end
endmodule
```

## Wavedump Tasks
Tasks for generating waveform files for post-simulation analysis.

### `$dumpfile`
Specifies the name of the dump file.

```SV
module dumpfile_example;
  initial begin
    $dumpfile("waveform.vcd");
  end
endmodule
```

### `$dumpvars`
Dumps the variables to the specified dump file.

```SV
module dumpvars_example;
  reg clk;
  initial begin
    $dumpfile("waveform.vcd");
    $dumpvars(0, dumpvars_example);
    clk = 0;
    forever #5 clk = ~clk;
  end
endmodule
```

## Time-related Tasks
Tasks for retrieving simulation time.

### `$time`
Returns the current simulation time as a 64-bit integer.

```SV
module time_example;
  initial begin
    $display("Current time: %0t", $time);
  end
endmodule
```

### `$stime`
Returns the current simulation time as a 32-bit integer.

```SV
module stime_example;
  initial begin
    $display("Current time (32-bit): %0d", $stime);
  end
endmodule
```

### `$realtime`
Returns the current simulation time as a real number.

```SV
module realtime_example;
  initial begin
    $display("Current time (real): %0f", $realtime);
  end
endmodule
```

## Simulation Control Tasks
Tasks for controlling the simulation.

### `$finish`
Terminates the simulation.

```SV
module finish_example;
  initial begin
    $display("Simulation will finish now.");
    $finish;
  end
endmodule
```

### `$stop`
Pauses the simulation.

```SV
module stop_example;
  initial begin
    $display("Simulation will stop now.");
    $stop;
  end
endmodule
```

### `$exit`
Terminates the simulation and exits the simulator.

```SV
module exit_example;
  initial begin
    $display("Simulation will exit now.");
    $exit;
  end
endmodule
```

## Exercises
1. Modify the `$display` example to display the current simulation time using `$time`.
2. Add another variable `b` to the `$monitor` example and monitor its changes along with `a`.
3. Modify the `$strobe` example to display a variable's value at the end of the time step.
4. Create a simple module and specify a dump file name using `$dumpfile`.
5. Add more variables to the `$dumpvars` example and dump them to the file.
6. Display the simulation time at multiple points in the `$time` example.
7. Compare the output of `$stime` with `$time`.
8. Use `$realtime` to display the time with a higher precision.
9. Add some delay before calling `$finish` in the `$finish` example.
10. Resume the simulation after stopping it in the `$stop` example.
11. Compare the behavior of `$exit` with `$finish`.

## Conclusion
Built-in system tasks and functions in SystemVerilog provide essential capabilities for displaying information, generating waveforms, retrieving simulation time, and controlling the simulation. Understanding and using these tasks effectively can greatly enhance the simulation and debugging process.
