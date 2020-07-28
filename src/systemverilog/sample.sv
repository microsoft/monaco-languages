module mux2to1 (input wire a, b, sel, // combined port and type declaration
                output logic y);
    always_comb begin // procedural block
        if (sel) y = a; // procedural statement
        else y = b;
    end
endmodule: mux2to1

program test (input clk, input [16:1] addr, inout [7:0] data);
initial begin
    data[2] <= addr[2]
endprogram

interface simple_bus(input logic clk); // Define the interface
    logic req, gnt;
    logic [7:0] addr, data;
    logic [1:0] mode;
    logic start, rdy;
endinterface: simple_bus

module memMod(simple_bus a); // simple_bus interface port
    timeunit 100ps / 10fs; // timeunit with optional second argument
    logic avail;
    // When memMod is instantiated in module top, a.req is the req
    // signal in the sb_intf instance of the ’simple_bus’ interface
    always @(posedge clk) a.gnt <= a.req & avail;
endmodule

module top;
    timeunit 100ps;
    timeprecision 10fs;
    logic clk = 0;
    simple_bus sb_intf(.clk(clk)); // Instantiate the interface
    memMod mem(.a(sb_intf)); // Connect interface to module instance
    cpuMod cpu(.b(sb_intf)); // Connect interface to module instance
endmodule

package ComplexPkg;
    typedef struct {
        shortreal i, r;
    } Complex;
    function Complex add(Complex a, b);
        add.r = a.r + b.r;
        add.i = a.i + b.i;
    endfunction
    function Complex mul(Complex a, b);
        mul.r = (a.r * b.r) - (a.i * b.i);
        mul.i = (a.r * b.i) + (a.i * b.r);
    endfunction
endpackage : ComplexPkg

`timescale 1ps/1ps
module top; // module with no ports
    logic in1, in2, select; // variable declarations
    wire out1; // net declaration
    mux2to1 m1 (.a(in1), .b(in2), .sel(select), .y(out1)); // module instance
endmodule: top

`timescale 1 ns / 10 ps
module mux2to1 (input wire a, b, sel, // combined port and type declaration
    output logic y);
    // netlist using built-in primitive instances
    not g1 (sel_n, sel);
    and g2 (a_s, a, sel_n);
    and g3 (b_s, b, sel);
    or g4 (y, a_s, b_s);
endmodule: mux2to1

task t;
    int x;
    x = 5 + b; // illegal - "b" is defined later
    x = 5 + $unit::b; // illegal - $unit adds no special forward referencing
endtask

module test;
    logic a;
    wire p;
    reg q;

    logic [1:0] shiftreg_a;
    bit [1:0]   busa_index;
    logic       error_condition;
    wire        merge_ab[100];
    logic [1:0] _bus3;
    logic [1:0] n$657;

    wire \busa+index ;
    logic \-clock ;
    bit \***error-condition*** ;
    reg [100:100] \net1/\net2 ;
    wire \{a,b} [8];
    reg \a*(b+c) ;
    wire \\/\/\signal$name ;

    assign n$657[1:0] = _bus3[1:0];

    always_comb
        begin
            \\/\/\signal$name = 1'b0;
            \***error-condition*** = \\/\/\signal$name ;
            \a*(b+c) = \a*(b+c) + '1;
        end

    initial begin
        a <= 0;
        a <= 1;
    end

    `define wordsize 8

    assign p = q;
    initial begin
        q = 1;
        #1 q = 0;
        $display(p);
        $display ("display a message");
        $finish;
    end
endmodule


module test;
  wire a = 659; // is a decimal number
  wire b = 'h 837FF; // is a hexadecimal number
  wire c = 'o7460; // is an octal number
  wire d = 4af; // is illegal (hexadecimal format requires 'h)

  wire e = 4'b1001; // is a 4-bit binary number
  wire f = 5 'D 3; // is a 5-bit decimal number
  wire g = 3'b01x; // is a 3-bit number with the least

  wire h = 12'hx; // is a 12-bit unknown number
  wire i = 16'hz; // is a 16-bit high-impedance number

  wire j = 8 'd -6; // this is illegal syntax
  wire k = -8 'd 6; // this defines the two's complement of 6,

  wire l = 4 'shf; // this denotes the 4-bit number '1111', to
                   // be interpreted as a 2's complement number,
                   // or '-1'. This is equivalent to -4'h 1
  wire m = -4 'sd15; // this is equivalent to -(-4'd 1), or '0001'
  wire n = 16'sd?; // the same as 16'sbz

endmodule : test

module test2;

    logic [11:0] a, b, c, d;
    logic [84:0] e, f, g;
    initial begin
        a = 'h x; // yields xxx
        b = 'h 3x; // yields 03x
        c = 'h z3; // yields zz3
        d = 'h 0z3; // yields 0z3
        e = 'h5; // yields {82{1'b0},3'b101}
        f = 'hx; // yields {85{1'hx}}
        g = 'hz; // yields {85{1'hz}}
    end

endmodule

module test3;

    logic [15:0] a, b, c, d;
    a = '0; // sets all 16 bits to 0
    b = '1; // sets all 16 bits to 1
    c = 'x; // sets all 16 bits to x
    d = 'z; // sets all 16 bits to z

    int e = 27_195_000 // unsized decimal 27195000
    wire [15:0] f = 16'b0011_0101_0001_1111 // 16-bit binary number
    wire [63:32] gg = 32 'h 12ab_f001 // 32-bit hexadecimal number

    real l, m, n, o, p, q, r, s, t;
    assign l = 1.2;
    assign m = 0.1;
    assign n = 2394.26331;
    assign o = 1.2E12; // (the exponent symbol can be e or E)
    assign p = 1.30e-2;
    assign q = 0.1e-0;
    assign r = 23E10;
    assign s = 29E-2;
    assign t = 236.123_763_e-12; // (underscores are ignored)

    bit [8*12:1] stringvar = "Hello world\n";
    bit [0:11] [7:0] stringvar = "Hello world\n" ;
    byte c3 [0:12] = "hello world\n" ;

    typedef struct {int a; shortreal b;} ab;
    ab c;
    c = '{0, 0.0}; // structure literal type determined from
                   // the left-hand context (c)
    ab abarr[1:0] = '{'{1, 1.0}, '{2, 2.0}};

    struct {int X,Y,Z;} XYZ = '{3{1}};
    typedef struct {int a,b[4];} ab_t;
    int a,b,c;
    ab_t v1[1:0] [2:0];
    v1 = '{2{'{3{'{a,'{2{b,c}}}}}}};

    int n[1:2][1:6] = '{2{'{3{4, 5}}}}; // same as '{'{4,5,4,5,4,5},'{4,5,4,5,4,5}}

    typedef int triple [1:3];
    $mydisplay(triple'{0,1,2});
    triple b = '{1:1, default:0}; // indices 2 and 3 assigned 0

endmodule : test3


module testAttributes;

    parameter IDLE = 2'd0;
    parameter READ = 2'd1;
    parameter DLY = 2'd2;

    logic [1:0] a, state;
    bit go;

    (* full_case, parallel_case *)
    case (a)
        state[IDLE]: if (go) next[READ] = 1'b1;
                     else next[IDLE] = 1'b1;
        state[READ]: next[DLY ] = 1'b1;
        state[DLY ]: if (!ws) next[DONE] = 1'b1;
                     else next[READ] = 1'b1;
        state[DONE]: next[IDLE] = 1'b1;

    (* full_case=1 *)
    (* parallel_case=1 *) // Multiple attribute instances also OK
    case (select[1:2])
        2'b00: result = 0;
        2'b01: result = flaga;
        2'b0x,
        2'b0z: result = flaga ? 'x : 0;
        2'b10: result = flagb;
        2'bx0,
        2'bz0: result = flagb ? 'x : 0;
        default result = 'x;
    endcase

    logic [7:0] ir;
    (* full_case, // no value assigned
    parallel_case=1 *)
    casez (ir)
        8'b1???????: instruction1(ir);
        8'b01??????: instruction2(ir);
        8'b00010???: instruction3(ir);
        8'b000001??: instruction4(ir);
    endcase

    logic [7:0] r, mask;
    mask = 8'bx0x0x0x0;
    (* full_case *) // parallel_case not specified
    casex (r ^ mask)
        8'b001100xx: stat1;
        8'b1100xx00: stat2;
        8'b00xx0011: stat3;
        8'bxx010100: stat4;
    endcase

    bit [2:0] a;
    unique case(a) // values 3,5,6,7 cause a violation report
        0,1: $display("0 or 1");
        2: $display("2");
        4: $display("4");
    endcase

    priority casez(a) // values 4,5,6,7 cause a violation report
        3’b00?: $display("0 or 1");
        3’b0??: $display("2 or 3");
    endcase

    always_comb begin
        not_a = !a;
    end

    always_comb begin : a1
        unique case (1’b1)
            a : z = b;
            not_a : z = c;
        endcase
    end

    (* optimize_power=0 *)
    mod1 synth1 (<port_list>);


    (* fsm_state *) logic [7:0] state1;
    (* fsm_state=1 *) logic [3:0] state2, state3;
    logic [3:0] reg1; // reg1 does NOT have fsm_state set
    (* fsm_state=0 *) logic [3:0] reg2; // nor does reg2

    a = b + (* mode = "cla" *) c; // sets the value for the attribute mode
    // to be the string cla.

    a = add (* mode = "cla" *) (b, c);

    a = b ? (* no_glitch *) c : d;

    parameter size = 8, longsize = 16;
    logic [size:1] opa, opb;
    logic [longsize:1] result;
    begin : mult
        logic [longsize:1] shift_opa, shift_opb;
        shift_opa = opa;
        shift_opb = opb;
        result = 0;
        repeat (size) begin
            if (shift_opb[1])
            result = result + shift_opa;
            shift_opa = shift_opa << 1;
            shift_opb = shift_opb >> 1;
        end
    end

endmodule

(* optimize_power *)
module mod1 (
    input clk
);

    trireg a; // trireg net of charge strength medium
    trireg (large) #(0,0,50) cap1; // trireg net of charge strength large
                                   // with charge decay time 50 time units
    trireg (small) signed [3:0] cap2; // signed 4-bit trireg vector of
                                      // charge strength small

endmodule : mod1

(* optimize_power=1 *)
module mod2;
    struct {
        bit [7:0] A;
        bit [7:0] B;
        byte C;
    } abc;

    assign abc.C = sel ? 8'hBE : 8'hEF;
    not (abc.A[0],abc.B[0]),
        (abc.A[1],abc.B[1]),
        (abc.A[2],abc.B[2]),
        (abc.A[3],abc.B[3]);

    always @(posedge clk) abc.B <= abc.B + 1;

    wire w = vara & varb; // net with a continuous assignment
    logic v = consta & constb; // variable with initialization
    logic vw; // no initial assignment
    assign vw = vara & varb; // continuous assignment to a variable
    real circ;
    assign circ = 2.0 * PI * R; // continuous assignment to a variable

    trireg (large) logic #(0,0,0) cap1;
    typedef logic [31:0] addressT;
    wire addressT w1;
    wire struct packed { logic ecc; logic [7:0] data; } memsig;

    var byte my_byte; // equivalent to "byte my_byte;"
    var v; // equivalent to "var logic v;"
    var [15:0] vw; // equivalent to "var logic [15:0] vw;"
    var enum bit { clear, error } status;
    input var logic data_in;
    var reg r;

    shortint s1, s2[0:9];

    int i = 0;

    tri1 scalared [63:0] bus64; //a bus that will be expanded
    tri vectored [31:0] data; //a bus that may or may not be expanded

    chandle variable_name ;

    byte c = "A"; // assigns to c "A"
    bit [10:0] b = "\x41"; // assigns to b ’b000_0100_0001
    bit [1:4][7:0] h = "hello" ; // assigns to h "ello"

    parameter string default_name = "John Smith";
    string myName = default_name;

endmodule

module test4;

    typedef logic [15:0] r_t;
    r_t r;
    integer i = 1;
    string b = "";
    string a = {"Hi", b};
    r = r_t'(a); // OK
    b = string’(r); // OK
    b = "Hi"; // OK
    b = {5{"Hi"}}; // OK
    a = {i{"Hi"}}; // OK (non-constant replication)
    r = {i{"Hi"}}; // invalid (non-constant replication)
    a = {i{b}}; // OK
    a = {a,b}; // OK
    a = {"Hi",b}; // OK
    r = {"H",""}; // yields "H\0". "" is converted to 8'b0
    b = {"H",""}; // yields "H". "" is the empty string
    a[0] = "h"; // OK, same as a[0] = "cough"
    a[0] = b; // invalid, requires a cast
    a[1] = "\0"; // ignored, a is unchanged

endmodule

interface intf_i;
    typedef int data_t;
endinterface

enum {red, yellow, green} light1, light2; // anonymous int type
// Syntax error: IDLE=2’b00, XX=2’bx <ERROR>, S1=2’b01, S2=2’b10
enum bit [1:0] {IDLE, XX=’x, S1=2’b01, S2=2’b10} state, next;
// Correct: IDLE=0, XX=’x, S1=1, S2=2
enum integer {IDLE, XX=’x, S1=’b01, S2=’b10} state, next;
// Syntax error: IDLE=0, XX=’x, S1=??, S2=??
enum integer {IDLE, XX=’x, S1, S2} state, next;
enum {bronze=3, silver, gold} medal; // silver=4, gold=5

// Correct declaration - bronze and gold are unsized
enum bit [3:0] {bronze='h3, silver, gold='h5} medal2;
// Correct declaration - bronze and gold sizes are redundant
enum bit [3:0] {bronze=4'h3, silver, gold=4'h5} medal3;

module mc #(int N = 5, M = N*16, type T = int, T x = 0)
    typedef enum {NO, YES} boolean;
    boolean myvar; // named type

    localparam byte colon1 = ":" ;
    specparam delay = 10 ; // specparams are used for specify blocks
    parameter logic flag = 1 ;

    typedef enum { red, green, blue, yellow } Colors;
    Colors c = c.first;
    forever begin
    $display( "%s : %d\n", c.name, c );
    if( c == c.last ) break;
    c = c.next;
    end

    parameter r2 = $;
    property inq1(r1,r2);
        @(posedge clk) a ##[r1:r2] b ##1 c |=> d;
    endproperty
    assert inq1(3);

endmodule

class vector #(size = 1); // size is a parameter in a parameter port list
    logic [size-1:0] v;
endclass
interface simple_bus #(AWIDTH = 64, type T = word) // parameter port list
    (input logic clk) ; // port list

endinterface

class Mem #(type T, int size);
    T words[size];
endclass

typedef Mem#(byte, 1024) Kbyte;

parameter msb = 7; // defines msb as a constant value 7
parameter e = 25, f = 9; // defines two constant numbers
parameter r = 5.7; // declares r as a real parameter
parameter byte_size = 8,
          byte_mask = byte_size - 1;
parameter average_delay = (r + f) / 2;
parameter signed [3:0] mux_selector = 0;
parameter real r1 = 3.5e17;
parameter p1 = 13'h7e;
parameter [31:0] dec_const = 1'b1; // value converted to 32 bits
parameter newconst = 3'h4; // implied range of [2:0]
parameter newconst = 4; // implied range of at least [31:0]



interface quiet_time_checker #(parameter min_quiet = 0,
                               parameter max_quiet = 0)
                              (input logic clk, reset_n, logic [1:0]en);
    generate
        if ( max_quiet == 0) begin
            property quiet_time;
                @(posedge clk) reset_n |-> ($countones(en) == 1);
            endproperty
            a1: assert property (quiet_time);
        end
        else begin
            property quiet_time;
                @(posedge clk)
                    (reset_n && ($past(en) != 0) && en == 0)
                    |->(en == 0)[*min_quiet:max_quiet]
                ##1 ($countones(en) == 1);
            endproperty
            a1: assert property (quiet_time);
        end
        if ((min_quiet == 0) && ($isunbounded(max_quiet))
            $display(warning_msg);
    endgenerate
endinterface

quiet_time_checker #(0, 0) quiet_never (clk,1,enables);
quiet_time_checker #(2, 4) quiet_in_window (clk,1,enables);
quiet_time_checker #(0, $) quiet_any (clk,1,enables);

interface width_checker #(parameter min_cks = 1, parameter max_cks = 1)
                         (input logic clk, reset_n, expr);
    generate
        if ($isunbounded(max_cks)) begin
            property width;
                @(posedge clk)
                (reset_n && $rose(expr)) |-> (expr [* min_cks]);
            endproperty
            a2: assert property (width);
        end
        else begin
            property assert_width_p;
                @(posedge clk)
                    (reset_n && $rose(expr)) |-> (expr[* min_cks:max_cks])
                    ##1 (!expr);
            endproperty
            a2: assert property (width);
        end
    endgenerate
endinterface

width_checker #(3, $) max_width_unspecified (clk,1,enables);
width_checker #(2, 4) width_specified (clk,1,enables);

module ma #( parameter p1 = 1, parameter type p2 = shortint )
           (input logic [p1:0] i, output logic [p1:0] o);
    p2 j = 0; // type of j is set by a parameter, (shortint unless redefined)
    always @(i) begin
        o = i;
        j++;
    end
endmodule

module mb;
    logic [3:0] i,o;
    typedef byte MEM_BYTES [256];
    typedef bit signed [7:0] MY_MEM_BYTES [256];
    ma #(.p1(3), .p2(int)) u1(i,o); //redefines p2 to a type of int
endmodule

specify
    specparam tRise_clk_q = 150, tFall_clk_q = 200;
    specparam tRise_control = 40, tFall_control = 50;
endspecify

module RAM16GEN ( output [7:0] DOUT,
                  input [7:0] DIN,
                  input [5:0] ADR,
                  input WE, CE);
    specparam dhold = 1.0;
    specparam ddly = 1.0;
    parameter width = 1;
    parameter regsize = dhold + 1.0; // Illegal - cannot assign
                                     // specparams to parameters
endmodule

module top_legal;
    int svar1 = 1; // static keyword optional
    initial begin
        for (int i=0; i<3; i++) begin
            automatic int loop3 = 0; // executes every loop
            for (int j=0; j<3; j++) begin
                loop3++;
                $display(loop3);
            end
        end // prints 1 2 3 1 2 3 1 2 3
        for (int i=0; i<3; i++) begin
            static int loop2 = 0; // executes once before time 0
            for (int j=0; j<3; j++) begin
                loop2++;
                $display(loop2);
            end
        end // prints 1 2 3 4 5 6 7 8 9
    end
endmodule : top_legal

program automatic test ;
    int i; // not within a procedural block - static
    task t ( int a ); // arguments and variables in t are automatic
    endtask
endprogram

package p1;
    typedef struct {int A;} t_1;
endpackage

typedef struct {int A;} t_2;

module sub();
    import p1::t_1;
    parameter type t_3 = int;
    parameter type t_4 = int;
    typedef struct {int A;} t_5;
    t_1 v1; t_2 v2; t_3 v3; t_4 v4; t_5 v5;
endmodule

module top();
    typedef struct {int A;} t_6;
    sub #(.t_3(t_6)) s1 ();
    sub #(.t_3(t_6)) s2 ();
    initial begin
        s1.v1 = s2.v1; // legal - both types from package p1 (rule 8)
        s1.v2 = s2.v2; // legal - both types from $unit (rule 4)
        s1.v3 = s2.v3; // legal - both types from top (rule 2)
        s1.v4 = s2.v4; // legal - both types are int (rule 1)
    end
    localparam type T = type(bit[12:0]);

    logic [7:0] regA;
    logic signed [7:0] regS;
    regA = unsigned'(-4); // regA = 8'b11111100
    regS = signed'(4'b1100); // regS = -4
endmodule


bit [12:0] A_bus, B_bus;
parameter type bus_t = type(A_bus);
generate
    case (type(bus_t))
        type(bit[12:0]): addfixed_int #(bus_t) (A_bus,B_bus);
        type(real): add_float #(type(A_bus)) (A_bus,B_bus);
    endcase
endgenerate

function Packet genPkt();
    Packet p;
    void'( randomize( p.address, p.length, p.payload )
        with { p.length > 1 && p.payload.size == p.length; } );
    p.chksum = p.payload.xor();
    return p;
endfunction

class x;
    Packet p;
    int size;
    size = channel[0] + 4;
    p = Packet'( channel[0 : size - 1] ); // convert stream to Packet
    channel = channel[ size : $ ]; // update the stream so it now
                                   // lacks that packe
endclass

typedef union packed { // default unsigned
    s_atmcell acell;
    bit [423:0] bit_slice;
    bit [52:0][7:0] byte_slice;
} u_atmcell;


module test6;
    u_atmcell u1;
    byte b; bit [3:0] nib;
    b = u1.bit_slice[415:408]; // same as b = u1.byte_slice[51];
    nib = u1.bit_slice [423:420]; // same as nib = u1.acell.GFC;

    bit signed [31:0] busA [7:0] ; // unpacked array of 8 32-bit vectors
    int busB [1:0]; // unpacked array of 2 integers
    busB = busA[7:6]; // select a 2-vector slice from busA

    int i = bitvec[j +: k]; // k must be constant.
    int a[x:y], b[y:z], e;
    a = {b[c -: d], e}; // d must be constant

    bit [3:0] nibble[]; // Dynamic array of 4-bit vectors
    integer mem[2][]; // Fixed-size unpacked array composed
    // of 2 dynamic subarrays of integers

    int arr1 [][2][3] = new [4]; // arr1 sized to length 4; elements are
                                 // fixed-size arrays and so do not require
                                 // initializing
    int arr2 [][] = new [4]; // arr2 sized to length 4; dynamic subarrays
                             // remain unsized and uninitialized
    int arr3 [1][2][] = new [4]; // Error – arr3 is not a dynamic array, though
                                 // it contains dynamic subarrays

    int src[], dest1[], dest2[];
    src = new [3] ('{2, 3, 4});
    dest1 = new[2] (src); // dest1’s elements are {2, 3}.
    dest2 = new[4] (src); // dest1’s elements are {2, 3, 4, 0}.

    logic [7:0] V1[10:1];
    logic [7:0] V2[10];
    wire [7:0] W[9:0]; // data type is logic [7:0] W[9:0]
    assign W = V1;
    initial #10 V2 = W;

    int B[] = new[100]; // dynamic array of 100 elements
    int C[] = new[8]; // dynamic array of 8 elements
    int D [3][][]; // multidimensional array with dynamic subarrays
    D[2] = new [2]; // initialize one of D’s dynamic subarrays
    D[2][0] = new [100];
    A[1] = B; // OK. Both are arrays of 100 ints
    A[1] = C; // type check error: different sizes (100 vs. 8 ints)
    A = D[2]; // A[0:1][100:1] and subarray D[2][0:1][0:99] both
              // comprise 2 subarrays of 100 ints

    string d[1:5] = '{ "a", "b", "c", "d", "e" };
    string p[];
    p = { d[1:3], "hello", d[4:5] };

    integer i_array[*]; // associative array of integer (unspecified
                        // index)
    bit [20:0] array_b[string]; // associative array of 21-bit vector,
                                // indexed by string
    event ev_array[myClass]; // associative

    int array_name1 [ integer ];
    typedef bit signed [4:1] SNibble;
    int array_name2 [ SNibble ];
    typedef bit [4:1] UNibble;
    int array_name3 [ UNibble ];

    typedef struct {byte B; int I[*];} Unpkt;
    int array_name [ Unpkt ];

    int map[ string ];
    map[ "hello" ] = 1;
    map[ "sad" ] = 2;
    map[ "world" ] = 3;
    map.delete( "sad" ); // remove entry whose index is "sad" from "map"
    map.delete; // remove all entries from the associative array "map"

    string s;
    forever begin
        if ( map.first( s ) )
            $display( "First entry is : map[ %s ] = %0d\n", s, map[s] );
        if ( map.last( s ) )
        do
            $display( "%s : %d\n", s, map[ s ] );
        while ( map.prev( s ) );
    end

    // an associative array of strings indexed by 2-state integers,
    // default is "hello".
    string words [int] = '{default: "hello"};
    // an associative array of 4-state integers indexed by strings, default is –1
    integer tab [string] = '{"Peter":20, "Paul":22, "Mary":23, default:-1 };

    byte q1[$]; // A queue of bytes
    string names[$] = { "Bob" }; // A queue of strings with one element
    integer Q[$] = { 3, 2, 7 }; // An initialized queue of integers
    bit q2[$:255]; // A queue whose maximum size is 256 bits

    typedef mytype element_t; // mytype is any legal type for a queue
    typedef element_t queue_t[$];
    element_t e;
    queue_t Q;
    int i;

    int q[$] = { 2, 4, 8 };
    int e, pos, junk;
    // assignment // method call yielding the
    // // same value in variable q
    // ----------------------------- // -------------------------
    q = { q, 6 }; // q.push_back(6)
    q = { e, q }; // q.push_front(e)
    q = q[1:$]; // q.pop_front(junk) or q.delete(0)
    q = q[0:$-1]; // q.pop_back(junk) or q.delete(q.size-1)
    q = { q[0:pos-1], e, q[pos:$] }; // q.insert(pos, e)
    q = { q[0:pos], e, q[pos+1:$] }; // q.insert(pos+1, e)
    q = {}; // q.delete()

    string SA[10], qs[$];
    int IA[int], qi[$];
    initial begin
        // Find all items greater than 5
        qi = IA.find( x ) with ( x > 5 );
        qi = IA.find( x ); // shall be an error
        // Find indices of all items equal to 3
        qi = IA.find_index with ( item == 3 );
        // Find first item equal to Bob
        qs = SA.find_first with ( item == "Bob" );
        // Find last item equal to Henry
        qs = SA.find_last( y ) with ( y == "Henry" );
        // Find index of last item greater than Z
        qi = SA.find_last_index( s ) with ( s > "Z" );
        // Find smallest item
        qi = IA.min;
        // Find string with largest numerical value
        qs = SA.max with ( item.atoi );
        // Find all unique string elements
        qs = SA.unique;
        // Find all unique strings in lowercase
        qs = SA.unique( s ) with ( s.tolower );
    end

    string s[] = { "hello", "sad", "world" };
    initial begin
        s.reverse; // s becomes { "world", "sad", "hello" };
        int q[$] = { 4, 5, 3, 1 };
        q.sort; // q becomes { 1, 3, 4, 5 }
        struct { byte red, green, blue; } c [512];
        c.sort with ( item.red ); // sort c using the red field only
        c.sort( x ) with ( {x.blue, x.green} ); // sort by blue then green
    end

    wire [5:0] inputs;
    initial begin
        inputs = 'b000000; // initialize at time zero
        #10 inputs = 'b011001; // first pattern
        #10 inputs = 'b011011; // second pattern
        #10 inputs = 'b011000; // third pattern
        #10 inputs = 'b001000; // last pattern
    end

    always_comb
        a = b & c;
    always_comb
        d <= #1ns b & c;

    always_latch
        if(ck) q <= d;

    always_ff @(posedge clock iff reset == 0 or posedge reset) begin
        r1 <= reset ? 0 : r2 + 1;
    end

    final
        begin
            $display("Number of cycles executed %d",$time/period);
            $display("Final PC = %h",PC);
        end

    parameter d = 50; // d declared as a parameter and
    logic [7:0] r; // r declared as an 8-bit variable
    begin // a waveform controlled by sequential delays
        #d r = 'h35;
        #d r = 'hE2;
        #d r = 'h00;
        #d r = 'hF7;
    end

    fork
    begin
        $display( "First Block\n" );
        # 20ns;
    end
    begin
        $display( "Second Block\n" );
        @eventA;
    end
    join

    initial
        for( int j = 1; j <= 3; ++j )
            fork
                automatic int k = j; // local copy, k, for each value of j
                #k $write( "%0d", k );
                begin
                    automatic int m = j; // the value of m is undetermined
                end
            join_none

    forkLabel: fork
        @enable_a
            begin
                #ta wa = 0;
                #ta wa = 1;
                #ta wa = 0;
            end
        @enable_b
            begin
                #tb wb = 1;
                #tb wb = 0;
                #tb wb = 1;
            end
    join : forkLabel

    forever @(negedge clock) rega = regb; // controlled by negedge on clock
    forever @(edge clock) rega = regb; // controlled by edge on clock

    always @(*) // equivalent to @(a or b or c or d or f)
        y = (a & b) | (c & d) | myfunction(f);

    always @* begin // equivalent to @(a or b or c or d or tmp1 or tmp2)
        tmp1 = a & b;
        tmp2 = c & d;
        y = tmp1 | tmp2;
    end

    always @* begin // same as @(a or en)
        y = 8'hff;
        y[a] = !en;
    end

endmodule

typedef union tagged {
    struct {
        bit [4:0] reg1, reg2, regd;
    } Add;
    union tagged {
        bit [9:0] JmpU;
        struct {
            bit [1:0] cc;
            bit [9:0] addr;
        } JmpC;
    } Jmp;
} Instr;

class testClass1;

    byte b[] = { 1, 2, 3, 4 };
    int y;
    y = b.sum ; // y becomes 10 => 1 + 2 + 3 + 4
    y = b.product ; // y becomes 24 => 1 * 2 * 3 * 4
    y = b.xor with ( item + 4 ); // y becomes 12 => 5 ^ 6 ^ 7 ^ 8
    logic [7:0] m [2][2] = '{ '{5, 10}, '{15, 20} };
    int y;
    y = m.sum with (item.sum with (item)); // y becomes 50 => 5+10+15+20
    logic bit_arr [1024];
    int y;

endclass

class Packet ;
    //data or class properties
    bit [3:0] command;
    bit [40:0] address;
    bit [4:0] master_id;
    integer time_requested;
    integer time_issued;
    integer status;
    // initialization
    function new();
        command = IDLE;
        address = 41'b0;
        master_id = 5'bx;
    endfunction
    // methods
    // public access entry points
    task clean();
        command = 0; address = 0; master_id = 5'bx;
    endtask
    task issue_request( int delay );
        // send request to bus
        endtask
        function integer current_status();
        current_status = status;
    endfunction
endclass

task task1(integer a, obj_example myexample);
    if (myexample == null) myexample = new;
endtask

class Packet;
    integer command;
    function new();
        command = IDLE;
    endfunction
endclass

class C;
    int c1 = 1;
    int c2 = 1;
    int c3 = 1;
    function new(int a);
        c2 = 2;
        c3 = a;
    endfunction
endclass

class D extends C;
    int d1 = 4;
    int d2 = c2;
    int d3 = 6;
    function new;
        super.new(d3);
    endfunction
endclass

function new(int cmd = IDLE, bit[12:0] adrs = 0, int cmd_time );
    command = cmd;
    address = adrs;
    time_requested = cmd_time;
endfunction

class baseA ;
    integer j = 5;
endclass

class B ;
    integer i = 1;
    baseA a = new;
endclass

class xtndA extends baseA;
    rand int x;
    constraint cst1 { x < 10; }
endclass

function integer test;
    xtndA xtnd1;
    baseA base2, base3;
    B b1 = new; // Create an object of class B
    B b2 = new b1; // Create an object that is a copy of b1
    b2.i = 10; // i is changed in b2, but not in b1
    b2.a.j = 50; // change a.j, shared by both b1 and b2
    test = b1.i; // test is set to 1 (b1.i has not changed)
    test = b1.a.j; // test is set to 50 (a.j has changed)
    xtnd1 = new; // create a new instance of class xtndA
    xtnd1.x = 3;
    base2 = xtnd1; // base2 refers to the same object as xtnd1
    base3 = new base2; // Creates a shallow copy of xtnd1
endfunction

lass Packet; // base class
    integer value;
    function integer delay();
        delay = value * value;
    endfunction
endclass
class LinkedPacket extends Packet; // derived class
    integer value;
    function integer delay();
        delay = super.delay()+ value * super.value;
    endfunction
endclass

class Jumbo_Packet;
    const int max_size = 9 * 1024; // global constant
    byte payload [];
    function new( int size );
        payload = new[ size > max_size ? max_size : size ];
    endfunction
endclass

class BasePacket;
    int A = 1;
    int B = 2;
    function void printA;
        $display("BasePacket::A is %d", A);
    endfunction : printA
    virtual function void printB;
        $display("BasePacket::B is %d", B);
    endfunction : printB
endclass : BasePacket
class My_Packet extends BasePacket;
    int A = 3;
    int B = 4;
    function void printA;
        $display("My_Packet::A is %d", A);
    endfunction: printA
    virtual function void printB;
        $display("My_Packet::B is %d", B);
    endfunction : printB
endclass : My_Packet

BasePacket P1 = new;
My_Packet P2 = new;

initial begin
    P1.printA; // displays 'BasePacket::A is 1'
    P1.printB; // displays 'BasePacket::B is 2'
    P1 = P2; // P1 has a handle to a My_packet object
    P1.printA; // displays 'BasePacket::A is 1'
    P1.printB; // displays 'My_Packet::B is 4' – latest derived method
    P2.printA; // displays 'My_Packet::A is 3'
    P2.printB; // displays 'My_Packet::B is 4'
end

virtual class BasePacket;
    pure virtual function integer send(bit[31:0] data); // No implementation
endclass

class Base;
    typedef enum {bin,oct,dec,hex} radix;
    static task print( radix r, integer n ); endtask
endclass

Base b = new;
int bin = 123;
b.print( Base::bin, bin ); // Base::bin and bin are different
Base::print( Base::hex, 66 );

class vector #(int size = 1);
    bit [size-1:0] a;
endclass

vector #(10) vten; // object with vector of size 10
vector #(.size(2)) vtwo; // object with vector of size 2
typedef vector#(4) Vfour; // Class with vector of size 4

sequence abc;
    @(posedge clk) a ##1 b ##1 c;
endsequence

sequence de;
    @(negedge clk) d ##[2:5] e;
endsequence

program check;
    initial begin
        wait( abc.triggered || de.triggered );
        if( abc.triggered )
            $display( "abc succeeded" );
        if( de.triggered )
            $display( "de succeeded" );
        end
endprogram

module test7;
    wire mynet ;
    assign (strong1, pull0) mynet = enable;

    wire #10 wireA;

endmodule

module adder (sum_out, carry_out, carry_in, ina, inb);
    output [3:0] sum_out;
    output carry_out;
    input [3:0] ina, inb;
    input carry_in;
    wire carry_out, carry_in;
    wire [3:0] sum_out, ina, inb;
    assign {carry_out, sum_out} = ina + inb + carry_in;
endmodule

module select_bus(busout, bus0, bus1, bus2, bus3, enable, s);
    parameter n = 16;
    parameter Zee = 16'bz;
    output [1:n] busout;
    input [1:n] bus0, bus1, bus2, bus3;
    input enable;
    input [1:2] s;
    tri [1:n] data; // net declaration
    // net declaration with continuous assignment
    tri [1:n] busout = enable ? data : Zee;
    // assignment statement with four continuous assignments
    assign
        data = (s == 0) ? bus0 : Zee,
        data = (s == 1) ? bus1 : Zee,
        data = (s == 2) ? bus2 : Zee,
        data = (s == 3) ? bus3 : Zee;
endmodule

module evaluates (out);
    output out;
    logic a, b, c;
    initial begin
        a = 0;
        b = 1;
        c = 0;
    end
    always c = #5 ~c;
    always @(posedge c) begin
        a <= b; // evaluates, schedules,
        b <= a; // and executes in two steps
    end
endmodule

module dff (q, d, clear, preset, clock);
    output q;
    input d, clear, preset, clock;
    logic q;
    always @(clear or preset)
        if (!clear)
            assign q = 0;
        else if (!preset)
            assign q = 1;
        else
            deassign q;
    always @(posedge clock)
        q = d;
endmodule

module test;
    logic a, b, c, d;
    wire e;

    and and1 (e, a, b, c);

    initial begin
        $monitor("%d d=%b,e=%b", $stime, d, e);
        assign d = a & b & c;
        a = 1;
        b = 0;
        c = 1;
        #10;
        force d = (a | b | c);
        force e = (a | b | c);
        #10;
        release d;
        release e;
        #10 $finish;
    end
endmodule

module byte_swap (inout wire [31:0] A, inout wire [31:0] B);
    alias {A[7:0],A[15:8],A[23:16],A[31:24]} = B;
endmodule

module byte_rip (inout wire [31:0] W, inout wire [7:0] LSB, MSB);
    alias W[7:0] = LSB;
    alias W[31:24] = MSB;

    wire a = 1'b1;

    always_comb begin
        unique0 if ((a==0) || (a==1)) $display("0 or 1");
        else if (a == 2) $display("2");
        else if (a == 4) $display("4"); // values 3,5,6,7
                                        // cause no violation report
    end

    always_comb begin : a1
        u1: unique if (a)
            z = a | b;
        else if (not_a)
            z = a | c;
    end

    always_comb begin : a1
    for (int j = 0; j < 3; j++)
        unique if (a[j])
            z[j] = a[j] | b[j];
        else if (not_a[j])
            z[j] = a[j] | c[j];
    end
endmodule

module traffic_lights;
    logic clock, red, amber, green;
    parameter on = 1, off = 0, red_tics = 350,
    amber_tics = 30, green_tics = 200;
    // initialize colors
    initial red = off;
    initial amber = off;
    initial green = off;
    always begin // sequence to control the lights
        red = on; // turn red light on
        light(red, red_tics); // and wait.
        green = on; // turn green light on
        light(green, green_tics); // and wait.
        amber = on; // turn amber light on
        light(amber, amber_tics); // and wait.
    end
    // task to wait for 'tics' positive edge clocks
    // before turning 'color' light off
    task light (output color, input [31:0] tics);
        repeat (tics) @ (posedge clock);
        color = off; // turn light off.
    endtask: light
    always begin // waveform for the clock
        #100 clock = 0;
        #100 clock = 1;
    end
endmodule: traffic_lights
