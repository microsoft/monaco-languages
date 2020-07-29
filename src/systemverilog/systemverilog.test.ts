/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

'use strict';

import { testTokenization } from '../test/testRunner';

testTokenization('systemverilog', [
	// Keywords
	[{
		line: 'module mux2to1 (input wire a, b, sel, output logic y);',
		tokens: [
			{ startIndex: 0,  type: 'keyword.module.sv'},
			{ startIndex: 6,  type: ''},
			{ startIndex: 7,  type: 'identifier.sv'},
			{ startIndex: 14, type: ''},
			{ startIndex: 15, type: 'delimiter.parenthesis.sv'},
			{ startIndex: 16, type: 'keyword.input.sv'},
			{ startIndex: 21, type: ''},
			{ startIndex: 22, type: 'keyword.wire.sv'},
			{ startIndex: 26, type: ''},
			{ startIndex: 27, type: 'identifier.sv'},
			{ startIndex: 28, type: 'delimiter.sv'},
			{ startIndex: 29, type: ''},
			{ startIndex: 30, type: 'identifier.sv'},
			{ startIndex: 31, type: 'delimiter.sv'},
			{ startIndex: 32, type: ''},
			{ startIndex: 33, type: 'identifier.sv'},
			{ startIndex: 36, type: 'delimiter.sv'},
			{ startIndex: 37, type: ''},
			{ startIndex: 38, type: 'keyword.output.sv' },
			{ startIndex: 44, type: ''},
			{ startIndex: 45, type: 'keyword.logic.sv' },
			{ startIndex: 50, type: ''},
			{ startIndex: 51, type: 'identifier.sv'},
			{ startIndex: 52, type: 'delimiter.parenthesis.sv'},
			{ startIndex: 53, type: 'delimiter.sv'}

		]
	}],

	[{
		line: 'assign enable = set & interrupt;',
		tokens: [
			{ startIndex: 0,  type: 'keyword.assign.sv'},
			{ startIndex: 6,  type: '' },
			{ startIndex: 7,  type: 'identifier.sv'},
			{ startIndex: 13, type: '' },
			{ startIndex: 14, type: 'delimiter.sv'},
			{ startIndex: 15, type: ''},
			{ startIndex: 16, type: 'identifier.sv'},
			{ startIndex: 19, type: '' },
			{ startIndex: 20, type: 'delimiter.sv'},
			{ startIndex: 21, type: ''},
			{ startIndex: 22, type: 'identifier.sv'},
			{ startIndex: 31, type: 'delimiter.sv'}
		]
	}],

	[{
		line: 'always_ff @(posedge clk) gnt <= req & avail;',
		tokens: [
			{ startIndex: 0,  type: 'keyword.always-ff.sv'},
			{ startIndex: 9,  type: '' },
			{ startIndex: 11, type: 'delimiter.parenthesis.sv'},
			{ startIndex: 12, type: 'keyword.posedge.sv'},
			{ startIndex: 19, type: ''},
			{ startIndex: 20, type: 'identifier.sv'},
			{ startIndex: 23, type: 'delimiter.parenthesis.sv'},
			{ startIndex: 24, type: ''},
			{ startIndex: 25, type: 'identifier.sv'},
			{ startIndex: 28, type: ''},
			{ startIndex: 29, type: 'delimiter.sv'},
			{ startIndex: 31, type: ''},
			{ startIndex: 32, type: 'identifier.sv'},
			{ startIndex: 35, type: ''},
			{ startIndex: 36, type: 'delimiter.sv'},
			{ startIndex: 37, type: ''},
			{ startIndex: 38, type: 'identifier.sv'},
			{ startIndex: 43, type: 'delimiter.sv'}
		]
	}],

	[{
		line: 'parameter type t_3 = int;',
		tokens: [
			{ startIndex: 0,  type: 'keyword.parameter.sv'},
			{ startIndex: 9,  type: ''},
			{ startIndex: 10, type: 'keyword.type.sv'},
			{ startIndex: 14, type: ''},
			{ startIndex: 15, type: 'identifier.sv'},
			{ startIndex: 18, type: ''},
			{ startIndex: 19, type: 'delimiter.sv'},
			{ startIndex: 20, type: ''},
			{ startIndex: 21, type: 'keyword.int.sv'},
			{ startIndex: 24, type: 'delimiter.sv'}
		]
	}],

	[{
		line: 'typedef union packed {',
		tokens: [
			{ startIndex: 0,  type: 'keyword.typedef.sv'},
			{ startIndex: 7, type: ''},
			{ startIndex: 8,  type: 'keyword.union.sv'},
			{ startIndex: 13, type: ''},
			{ startIndex: 14, type: 'keyword.packed.sv'},
			{ startIndex: 20, type: ''},
			{ startIndex: 21, type: 'delimiter.curly.sv'}
		]
	}],

	[{
		line: 'a = 8\'hFF;',
		tokens: [
			{ startIndex: 0, type: 'identifier.sv' },
			{ startIndex: 1, type: ''},
			{ startIndex: 2, type: 'delimiter.sv'},
			{ startIndex: 3, type: ''},
			{ startIndex: 4, type: 'number.sv'},
			{ startIndex: 5, type: 'number.hex.sv'},
			{ startIndex: 9, type: 'delimiter.sv'}
		]
	}],

	[{
		line: 'a = 2\'b01;',
		tokens: [
			{ startIndex: 0, type: 'identifier.sv' },
			{ startIndex: 1, type: ''},
			{ startIndex: 2, type: 'delimiter.sv'},
			{ startIndex: 3, type: ''},
			{ startIndex: 4, type: 'number.sv'},
			{ startIndex: 5, type: 'number.binary.sv'},
			{ startIndex: 9, type: 'delimiter.sv'}
		]
	}],

	[{
		line: 'a = 6\'o654;',
		tokens: [
			{ startIndex: 0, type: 'identifier.sv' },
			{ startIndex: 1, type: ''},
			{ startIndex: 2, type: 'delimiter.sv'},
			{ startIndex: 3, type: ''},
			{ startIndex: 4, type: 'number.sv'},
			{ startIndex: 5, type: 'number.octal.sv'},
			{ startIndex: 10, type: 'delimiter.sv'}
		]
	}],

	[{
		line: 'a = 8\'d98;',
		tokens: [
			{ startIndex: 0, type: 'identifier.sv' },
			{ startIndex: 1, type: ''},
			{ startIndex: 2, type: 'delimiter.sv'},
			{ startIndex: 3, type: ''},
			{ startIndex: 4, type: 'number.sv'},
			{ startIndex: 9, type: 'delimiter.sv'}
		]
	}],

	[{
		line: '10\'bxxxx_zxxxx',
		tokens: [
			{ startIndex: 0, type: 'number.sv'},
			{ startIndex: 2, type: 'number.binary.sv' }
		]
	}],

	[{
		line: '1\'H?z',
		tokens: [
			{ startIndex: 0, type: 'number.sv'},
			{ startIndex: 1, type: 'number.hex.sv' }
		]
	}],

	[{
		line: '64E435456',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '64.4e3445',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv'}
		]
	}],

	[{
		line: 'if( my_var[3:0] == 4\'b0101)',
		tokens: [
			{ startIndex: 0,  type: 'keyword.if.sv'},
			{ startIndex: 2,  type: 'delimiter.parenthesis.sv'},
			{ startIndex: 3,  type: ''},
			{ startIndex: 4,  type: 'identifier.sv'},
			{ startIndex: 10, type: 'delimiter.square.sv'},
			{ startIndex: 11, type: 'number.sv'},
			{ startIndex: 12, type: 'delimiter.sv'},
			{ startIndex: 13, type: 'number.sv'},
			{ startIndex: 14, type: 'delimiter.square.sv'},
			{ startIndex: 15, type: '' },
			{ startIndex: 16, type: 'delimiter.sv'},
			{ startIndex: 18, type: ''},
			{ startIndex: 19, type: 'number.sv'},
			{ startIndex: 20, type: 'number.binary.sv'},
			{ startIndex: 26, type: 'delimiter.parenthesis.sv'}
		]
	}],

	[{
		line: 'typedef enum int {FAST_SIM = 0, RANDOM = 1, NOMINAL = 2, START_UP = 3} clock_plan_e;',
		tokens: [
			{ startIndex: 0,  type: 'keyword.typedef.sv'},
			{ startIndex: 7,  type: ''},
			{ startIndex: 8,  type: 'keyword.enum.sv'},
			{ startIndex: 12, type: ''},
			{ startIndex: 13, type: 'keyword.int.sv'},
			{ startIndex: 16, type: ''},
			{ startIndex: 17, type: 'delimiter.curly.sv'},
			{ startIndex: 18, type: '' },
			{ startIndex: 22, type: 'identifier.sv' },
			{ startIndex: 26, type: '' },
			{ startIndex: 27, type: 'delimiter.sv' },
			{ startIndex: 28, type: '' },
			{ startIndex: 29, type: 'number.sv' },
			{ startIndex: 30, type: 'delimiter.sv' },
			{ startIndex: 31, type: '' },
			{ startIndex: 39, type: 'delimiter.sv' },
			{ startIndex: 40, type: '' },
			{ startIndex: 41, type: 'number.sv' },
			{ startIndex: 42, type: 'delimiter.sv' },
			{ startIndex: 43, type: '' },
			{ startIndex: 52, type: 'delimiter.sv' },
			{ startIndex: 53, type: '' },
			{ startIndex: 54, type: 'number.sv' },
			{ startIndex: 55, type: 'delimiter.sv' },
			{ startIndex: 56, type: '' },
			{ startIndex: 62, type: 'identifier.sv' },
			{ startIndex: 65, type: '' },
			{ startIndex: 66, type: 'delimiter.sv' },
			{ startIndex: 67, type: '' },
			{ startIndex: 68, type: 'number.sv' },
			{ startIndex: 69, type: 'delimiter.curly.sv' },
			{ startIndex: 70, type: '' },
			{ startIndex: 71, type: 'identifier.sv' },
			{ startIndex: 83, type: 'delimiter.sv' }
		]
	}],

	[{
		line: 'if( my_var[31:0] === 32\'h2aB0_113C )',
		tokens: [
			{ startIndex: 0,  type: 'keyword.if.sv'},
			{ startIndex: 2,  type: 'delimiter.parenthesis.sv'},
			{ startIndex: 3,  type: ''},
			{ startIndex: 4,  type: 'identifier.sv'},
			{ startIndex: 10, type: 'delimiter.square.sv'},
			{ startIndex: 11, type: 'number.sv'},
			{ startIndex: 13, type: 'delimiter.sv'},
			{ startIndex: 14, type: 'number.sv'},
			{ startIndex: 15, type: 'delimiter.square.sv'},
			{ startIndex: 16, type: ''},
			{ startIndex: 21, type: 'number.sv'},
			{ startIndex: 23, type: 'number.hex.sv'},
			{ startIndex: 34, type: ''},
			{ startIndex: 35, type: 'delimiter.parenthesis.sv'}
		]
	}],
  
	// Include tests
	[{
		line: '`include"tb_test.sv"',
		tokens: [
			{ startIndex: 0, type: 'keyword.directive.include.sv'},
			{ startIndex: 8, type: 'keyword.directive.include.begin.sv'},
			{ startIndex: 9, type: 'string.include.identifier.sv'},
			{ startIndex: 19, type: 'keyword.directive.include.end.sv'}
		]
	}, {
		line: '`include "path/to/my/file.sv"',
		tokens: [
			{ startIndex: 0, type: 'keyword.directive.include.sv'},
			{ startIndex: 8, type: ''},
			{ startIndex: 9, type: 'keyword.directive.include.begin.sv'},
			{ startIndex: 10, type: 'string.include.identifier.sv'},
			{ startIndex: 28, type: 'keyword.directive.include.end.sv'}
		]
	}, {
		line: '`include                      "file.sv"',
		tokens: [
			{ startIndex: 0, type: 'keyword.directive.include.sv'},
			{ startIndex: 8, type: ''},
			{ startIndex: 30, type: 'keyword.directive.include.begin.sv'},
			{ startIndex: 31, type: 'string.include.identifier.sv'},
			{ startIndex: 38, type: 'keyword.directive.include.end.sv'}
		]
	}, {
		line: '   `include "file.sv"',
		tokens: [
			{ startIndex: 0, type: ''},
			{ startIndex: 3, type: 'keyword.directive.include.sv'},
			{ startIndex: 11, type: ''},
			{ startIndex: 12, type: 'keyword.directive.include.begin.sv'},
			{ startIndex: 13, type: 'string.include.identifier.sv'},
			{ startIndex: 20, type: 'keyword.directive.include.end.sv'}
		]
	}, {
		line: '   `include     "file.sv"',
		tokens: [
			{ startIndex: 0, type: ''},
			{ startIndex: 3, type: 'keyword.directive.include.sv'},
			{ startIndex: 11, type: ''},
			{ startIndex: 16, type: 'keyword.directive.include.begin.sv'},
			{ startIndex: 17, type: 'string.include.identifier.sv'},
			{ startIndex: 24, type: 'keyword.directive.include.end.sv'}
		]
	}, {
    line: '`include<tb_test.sv>',
		tokens: [
			{ startIndex: 0, type: 'keyword.directive.include.sv'},
			{ startIndex: 8, type: 'keyword.directive.include.begin.sv'},
			{ startIndex: 9, type: 'string.include.identifier.sv'},
			{ startIndex: 19, type: 'keyword.directive.include.end.sv'}
		]
	}, {
		line: '`include <path/to/my/file.sv>',
		tokens: [
			{ startIndex: 0, type: 'keyword.directive.include.sv'},
			{ startIndex: 8, type: ''},
			{ startIndex: 9, type: 'keyword.directive.include.begin.sv'},
			{ startIndex: 10, type: 'string.include.identifier.sv'},
			{ startIndex: 28, type: 'keyword.directive.include.end.sv'}
    ],
  }],

	// Preprocessor Directives
	[{
		line: '`__FILE__',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier.sv'}
		]
	}, {
		line: '      `begin_keywords',
		tokens: [
			{ startIndex: 0, type: ''},
			{ startIndex: 6, type: 'keyword.sv'},
			{ startIndex: 7, type: 'identifier.sv'}
		]
	}, {
		line: '`define wordsize 8',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier.sv'},
			{ startIndex: 7, type: ''},
			{ startIndex: 8, type: 'identifier.sv'},
			{ startIndex: 16, type: ''},
			{ startIndex: 17, type: 'number.sv'}
		]
	}, {
		line: '`      else',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: ''},
			{ startIndex: 7, type: 'identifier.sv'}
		]
	}, {
		line: '`timescale 1ns/1ps',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier'},
			{ startIndex: 10, type: ''},
			{ startIndex: 11, type: 'number.sv'},
			{ startIndex: 12, type: 'identifier.sv'}
		]
	}, {
		line: '`timescale 1 ns / 1 ps',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier'},
			{ startIndex: 10, type: ''},
			{ startIndex: 11, type: 'number.sv'},
			{ startIndex: 12, type: ''},
			{ startIndex: 13, type: 'identifier.sv'},
			{ startIndex: 15, type: ''},
			{ startIndex: 16, type: 'identifier.sv'},
			{ startIndex: 17, type: ''},
			{ startIndex: 18, type: 'number.sv'},
			{ startIndex: 19, type: ''},
			{ startIndex: 20, type: 'identifier.sv'},
		]
	}, {
		line: '`MACRO (1, 2, 3)',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier.sv'},
			{ startIndex: 6, type: ''},
			{ startIndex: 7, type: 'delimiter.parenthesis.sv'},
			{ startIndex: 8, type: 'number.sv'},
			{ startIndex: 9, type: 'delimiter.sv'},
			{ startIndex: 10, type: ''},
			{ startIndex: 11, type: 'number.sv'},
			{ startIndex: 12, type: 'delimiter.sv'},
			{ startIndex: 13, type: ''},
			{ startIndex: 14, type: 'number.sv'},
			{ startIndex: 15, type: 'delimiter.parenthesis.sv'},
		]
	}, {
		line: '`ifdef wow',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier.sv'},
			{ startIndex: 6, type: ''},
			{ startIndex: 7, type: 'identifier'}
		]
	}, {
		line: '`ifndef AGENT',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier.sv'},
			{ startIndex: 7, type: ''},
			{ startIndex: 8, type: 'identifier.sv'}
		]
	}, {
		line: '`endif // AGENT',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier.sv'},
			{ startIndex: 6, type: ''},
			{ startIndex: 7, type: 'comment.sv'}
		]
	}, {
		line: '`pragma protect encoding=(enctype="raw")',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier.sv'},
			{ startIndex: 7, type: ''},
			{ startIndex: 8, type: 'identifier.sv'},
			{ startIndex: 15, type: ''},
			{ startIndex: 16, type: 'identifier.sv'},
			{ startIndex: 24, type: 'delimiter.sv'},
			{ startIndex: 25, type: 'delimiter.parenthesis.sv'},
			{ startIndex: 26, type: 'identifier.sv'},
			{ startIndex: 33, type: 'delimiter.sv'},
			{ startIndex: 34, type: 'string.sv'},
			{ startIndex: 39, type: 'delimiter.parenthesis.sv'}
		]
	}, {
		line: '`undef macro_name',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier.sv'},
			{ startIndex: 6, type: ''},
			{ startIndex: 7, type: 'identifier.sv'}
		]
	}, {
		line: '`celldefine    ',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier,sv'},
			{ startIndex: 11, type: ''}
		]
	}, {
		line: '`default_nettype none',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv'},
			{ startIndex: 1, type: 'identifier'},
			{ startIndex: 16, type: ''},
			{ startIndex: 17, type: 'identifier.sv'}
		]
	}]  
]);

