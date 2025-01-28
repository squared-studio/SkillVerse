# Task 19 : Testbench Example

## Documentation
### [Click here to see the Design Documentation](https://github.com/DSi-DV/rv64g-core/blob/main/document/rtl/pipeline.md)

## RTL
### [Click here to see the latest RTL](https://github.com/DSi-DV/rv64g-core/blob/main/source/pipeline.sv)
```SV
module pipeline #(
    parameter int DW = 8  // Data width parameter
) (
    input logic arst_ni,  // Asynchronous reset, active low
    input logic clk_i,    // Clock input
    input logic clear_i,  // Synchronous clear signal

    input  logic [DW-1:0] data_in_i,        // Input data
    input  logic          data_in_valid_i,  // Input data valid signal
    output logic          data_in_ready_o,  // Input data ready signal

    output logic [DW-1:0] data_out_o,        // Output data
    output logic          data_out_valid_o,  // Output data valid signal
    input  logic          data_out_ready_i   // Output data ready signal
);

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-SIGNALS
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // Flag to indicate if the pipeline stage is full
  logic is_full;

  // Handshake signal for input data
  logic input_handshake;

  // Handshake signal for output data
  logic output_handshake;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-ASSIGNMENTS
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // Ready if not reset/clear and either not full or output is ready
  always_comb data_in_ready_o = arst_ni & ~clear_i & ((is_full) ? data_out_ready_i : '1);

  // Output is valid if the stage is full and is not reset/clear
  always_comb data_out_valid_o = is_full & arst_ni & ~clear_i;

  // Handshake condition for input data
  always_comb input_handshake = data_in_valid_i & data_in_ready_o;

  // Handshake condition for output data
  always_comb output_handshake = data_out_valid_o & data_out_ready_i;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-SEQUENTIALS
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // Latch input data to output on positive clock edge if handshake is successful
  always_ff @(posedge clk_i) begin
    if (input_handshake) begin
      data_out_o <= data_in_i;
    end
  end

  // Control the is_full flag based on reset, clear, input, and output handshake signals
  always_ff @(posedge clk_i or negedge arst_ni) begin : main_block
    if (~arst_ni) begin
      is_full <= '0;  // Reset the is_full flag when asynchronous reset is active
    end else begin
      // Determine the next state of is_full based on the current clear, input handshake, and
      // output handshake signals
      casex ({
        clear_i, input_handshake, output_handshake
      })
        3'b1xx, 3'b001: is_full <= '0;
        3'b010, 3'b011: is_full <= '1;
        default: is_full <= is_full;
      endcase
    end
  end

endmodule
```

## Testbench
### [Click here to see the latest Testbench](https://github.com/DSi-DV/rv64g-core/blob/main/test/pipeline_tb/pipeline_tb.sv)
```SV
module pipeline_tb;  // Testbench module for the pipeline

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-LOCALPARAMS
  //////////////////////////////////////////////////////////////////////////////////////////////////

  localparam int DW = 8;  // Local parameter for data width

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-TYPEDEFS
  //////////////////////////////////////////////////////////////////////////////////////////////////

  typedef logic [DW-1:0] data_t;  // Type definition for data based on data width

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-SIGNALS
  //////////////////////////////////////////////////////////////////////////////////////////////////

  logic arst_ni;  // Asynchronous reset signal
  logic clk_i;  // Clock signal

  logic clear_i;  // Clear signal
  data_t data_in_i;  // Data input signal
  logic data_in_valid_i;  // Data input valid signal
  logic data_in_ready_o;  // Data input ready signal
  data_t data_out_o;  // Data output signal
  logic data_out_valid_o;  // Data output valid signal
  logic data_out_ready_i;  // Data output ready signal

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-VARIABLES
  //////////////////////////////////////////////////////////////////////////////////////////////////

  event e_buffer_clear;  // Event for buffer clear
  event e_push_only;  // Event for push only
  event e_pop_only;  // Event for pop only
  event e_push_pop;  // Event for push and pop

  bit in_out_ok;  // Flag to check if input matches output
  int tx_success;  // Counter for successful data transfers

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-RTLS
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // Instantiate the pipeline module with the specified data width parameter
  pipeline #(
      .DW(DW)
  ) u_pipeline (
      .arst_ni,  // Asynchronous reset signal
      .clk_i,  // Clock signal
      .clear_i,  // Clear signal
      .data_in_i,  // Data input signal
      .data_in_valid_i,  // Data input valid signal
      .data_in_ready_o,  // Data input ready signal
      .data_out_o,  // Data output signal
      .data_out_valid_o,  // Data output valid signal
      .data_out_ready_i  // Data output ready signal
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-METHODS
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // Task to apply reset to the module
  task static apply_reset();

    assert (data_in_ready_o === 'x)  // Assert that data_in_ready_o is unknown before reset
    else $error("data_in_ready_o X at before reset");  // Report error if assertion fails

    assert (data_out_valid_o === 'x)  // Assert that data_out_valid_o is unknown before reset
    else $error("data_out_valid_o X at before reset");  // Report error if assertion fails

    #100ns;  // Wait for 100 nanoseconds

    arst_ni          <= '0;  // Deassert asynchronous reset (active low)
    clk_i            <= '0;  // Initialize clock signal to 0
    clear_i          <= '0;  // Deassert clear signal
    data_in_i        <= '0;  // Initialize data input to 0
    data_in_valid_i  <= '0;  // Deassert data input valid signal
    data_out_ready_i <= '0;  // Deassert data output ready signal

    #100ns;  // Wait for 100 nanoseconds

    assert (data_in_ready_o === '0)  // Assert that data_in_ready_o is 0 during reset
    else $error("data_in_ready_o 0 during reset");  // Report error if assertion fails

    assert (data_out_valid_o === '0)  // Assert that data_out_valid_o is 0 during reset
    else $error("data_out_valid_o 0 during reset");  // Report error if assertion fails

    arst_ni <= 1;  // Assert asynchronous reset

    #100ns;  // Wait for 100 nanoseconds

    assert (data_in_ready_o === '1)  // Assert that data_in_ready_o is 1 after reset
    else $error("data_in_ready_o 1 after reset");  // Report error if assertion fails

    assert (data_out_valid_o === '0)  // Assert that data_out_valid_o is 0 after reset
    else $error("data_out_valid_o 0 after reset");  // Report error if assertion fails

  endtask

  // Task to start the clock signal
  task static start_clk_i();
    fork  // Start a parallel forever block
      forever begin
        clk_i <= '1;  // Set clock signal to 1
        #5ns;  // Wait for 5 nanoseconds
        clk_i <= '0;  // Set clock signal to 0
        #5ns;  // Wait for 5 nanoseconds
      end
    join_none  // Do not wait for the forked tasks to complete
  endtask

  // Task to clear the pipeline
  task automatic clear();
    clear_i <= '1;  // Assert clear signal
    @(posedge clk_i);  // Wait for the positive edge of the clock signal
    clear_i <= '0;  // Deassert clear signal
  endtask

  // Task to start input-output monitoring
  task automatic start_in_out_mon();

    data_t in__;  // Temporary variable for input data
    data_t out__;  // Temporary variable for output data

    mailbox #(data_t) in_mbx = new();  // Mailbox for input data
    mailbox #(data_t) out_mbx = new();  // Mailbox for output data

    in_out_ok  = 1;  // Initialize input-output match flag
    tx_success = 0;  // Initialize successful transfers counter


    fork  // Start a parallel block
      forever begin  // Loop indefinitely

        // Wait for the positive edge of the clock signal or the negative edge of the asynchronous
        // reset signal
        @(posedge clk_i or negedge arst_ni);

        // If asynchronous reset is asserted and clear is deasserted
        if (arst_ni && ~clear_i) begin

          // If data input is valid and ready, put data into input mailbox
          if (data_in_valid_i === 1 && data_in_ready_o === 1) begin
            in_mbx.put(data_in_i);
          end

          // If data output is valid and ready, put data into output mailbox
          if (data_out_valid_o === 1 && data_out_ready_i === 1) begin
            out_mbx.put(data_out_o);
          end

          // If both mailboxes have data
          if (in_mbx.num() && out_mbx.num()) begin

            // Get data from input mailbox
            in_mbx.get(in__);

            // Get data from output mailbox
            out_mbx.get(out__);

            // If input data does not match output data, set input-output match flag to 0
            if (in__ !== out__) begin
              in_out_ok = 0;
            end else begin  // Otherwise, increment successful transfers counter
              tx_success++;
            end

          end

        end else begin  // If asynchronous reset is deasserted or clear is asserted
          while (in_mbx.num()) in_mbx.get(in__);  // Clear input mailbox
          while (out_mbx.num()) out_mbx.get(out__);  // Clear output mailbox
        end

      end
    join_none  // Do not wait for the forked tasks to complete
  endtask

  // Task to start random drive on inputs
  task automatic start_random_drive();
    fork  // Start a parallel block
      forever begin  // Loop indefinitely
        // Wait for the positive edge of the clock signal
        @(posedge clk_i);
        // 2% odds of asserting clear signal
        clear_i <= ($urandom_range(0, 99) < 2);
        // Set data input to a random value
        data_in_i <= $urandom;
        // 50% odds of asserting data input valid signal
        data_in_valid_i <= ($urandom_range(0, 99) < 50);
        // 50% odds of asserting data output ready signal
        data_out_ready_i <= ($urandom_range(0, 99) < 50);
      end
    join_none  // Do not wait for the forked tasks to complete
  endtask

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-SEQUENTIALS
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // Sequential block to trigger buffer clear event if clear signal is asserted and not in reset
  always @(posedge clk_i iff (arst_ni & clear_i)) begin
    ->e_buffer_clear;  // Trigger buffer clear event
  end

  // Sequential block to trigger push only event if not clearing
  always @(posedge clk_i iff (arst_ni & ~clear_i)) begin
    // If data is being pushed into the pipeline without any data being popped
    if ((data_in_valid_i & data_in_ready_o & ~data_out_valid_o) === 1) begin
      ->e_push_only;  // Trigger push only event
    end
  end

  // Sequential block to trigger pop only event if not clearing
  always @(posedge clk_i iff (arst_ni & ~clear_i)) begin
    // If data is being popped from the pipeline without any data being pushed
    if ((~data_in_valid_i & data_out_valid_o & data_out_ready_i) === 1) begin
      ->e_pop_only;  // Trigger pop only event
    end
  end

  // Sequential block to trigger push and pop event if not clearing
  always @(posedge clk_i iff (arst_ni & ~clear_i)) begin
    // If data is being both pushed into and popped from the pipeline
    if ((data_in_valid_i & data_in_ready_o & data_out_valid_o & data_out_ready_i) === 1) begin
      ->e_push_pop;  // Trigger push and pop event
    end
  end

  //////////////////////////////////////////////////////////////////////////////////////////////////
  //-PROCEDURALS
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // Initial block to handle fatal timeout
  initial begin
    #1ms;
    $fatal(1, "FATAL TIMEOUT");  // Terminate simulation with a fatal error after 1ms
  end

  // Initial block to apply reset, start clock, monitor & drive
  initial begin
    apply_reset();  // Apply the reset task to initialize the pipeline
    start_clk_i();  // Start the clock signal
    start_in_out_mon();  // Start monitoring the input-output data
    start_random_drive();  // Start driving random values to the inputs
  end

  // Initial block to handle events and display results
  initial begin
    fork
      begin
        repeat (100) @(e_buffer_clear);  // Wait for 100 buffer clear events
        $display("Pipeline Clear - applied");  // Display message after 100 buffer clear events
      end
      begin
        repeat (100) @(e_push_only);  // Wait for 100 push only events
        $display("Pipeline Push only - applied");  // Display message after 100 push only events
      end
      begin
        repeat (100) @(e_pop_only);  // Wait for 100 pop only events
        $display("Pipeline Pop only - applied");  // Display message after 100 pop only events
      end
      begin
        repeat (100) @(e_push_pop);  // Wait for 100 push and pop events
        $display("Pipeline Push Pop - applied");  // Display message after 100 push and pop events
      end
    join

    if (in_out_ok && tx_success) begin
      $display("Data integrity OK. %0d transfers successful",
               tx_success);  // Display success message if data integrity is maintained
    end

    $finish;  // Terminate the simulation

  end

endmodule  // End of testbench module

```
