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
	// Strings
	[{
		line: 'pdisplay ("display msg");',
		tokens: [
			{ startIndex: 0, type: 'identifier.sv'},
			{ startIndex: 8, type: ''},
			{ startIndex: 9,  type: 'delimiter.parenthesis.sv'},
			{ startIndex: 10, type: 'string.sv'},
			{ startIndex: 22,  type: 'string.escape.sv'},
			{ startIndex: 23,  type: 'delimiter.parenthesis.sv'},
			{ startIndex: 24, type: 'delimiter.sv'},
		]
	}],
	[{
		line: '"multi\n line\n string"',
		tokens: [
			{ startIndex: 0, type: 'string.sv'},
			{ startIndex: 6, type: 'string.escape.sv'},
			{ startIndex: 8, type: 'string.sv'},
			{ startIndex: 13, type: 'string.escape.sv'},
			{ startIndex: 15, type: 'string.sv'},
			{ startIndex: 22,  type: 'string.escape.sv'},
		]
	}],
	[{
		line: 'pdisplay ("%s : %d\n", c.name, c );',
		tokens: [
			{ startIndex: 0, type: 'identifier.sv'},
			{ startIndex: 8, type: ''},
			{ startIndex: 9,  type: 'delimiter.parenthesis.sv'},
			{ startIndex: 10, type: 'string.sv'},
			{ startIndex: 18, type: 'string.escape.sv'},
			{ startIndex: 21, type: 'delimiter.sv'},
			{ startIndex: 22, type: ''},
			{ startIndex: 23, type: 'identifier.sv'},
			{ startIndex: 24, type: 'delimiter.sv'},
			{ startIndex: 25, type: 'identifier.sv'},
			{ startIndex: 29, type: 'delimiter.sv'},
			{ startIndex: 30, type: ''},
			{ startIndex: 31, type: 'identifier.sv'},
			{ startIndex: 32, type: ''},
			{ startIndex: 33,  type: 'delimiter.parenthesis.sv'},
			{ startIndex: 34, type: 'delimiter.sv'},
		]
	}],
	[{
		line: 'var lexvar = "Color is \xddblue";',
		tokens: [
			{ startIndex: 0, type: 'keyword.var.sv'},
			{ startIndex: 3, type: ''},
			{ startIndex: 4, type: 'identifier.sv'},
			{ startIndex: 10, type: ''},
			{ startIndex: 11, type: 'delimiter.sv'},
			{ startIndex: 12, type: ''},
			{ startIndex: 13, type: 'string.sv'},
			{ startIndex: 23, type: 'string.escape.sv'},
			{ startIndex: 27, type: 'string.sv'},
			{ startIndex: 32,  type: 'string.escape.sv'},
		]
	}],
	[{
		line: '"Valid escapes \b \f \v"',
		tokens: [
			{ startIndex: 0, type: 'string.sv'},
			{ startIndex: 15, type: 'string.escape.sv'},
			{ startIndex: 17, type: 'string.sv'},
			{ startIndex: 18, type: 'string.escape.sv'},
			{ startIndex: 20, type: 'string.sv'},
			{ startIndex: 21,  type: 'string.escape.sv'},
		]
	}],
	[{
		line: '"Valid escapes \o \j \z"',
		tokens: [
			{ startIndex: 0, type: 'string.sv'},
			{ startIndex: 15, type: 'string.escape.invalid.sv'},
			{ startIndex: 17, type: 'string.sv'},
			{ startIndex: 18, type: 'string.escape.invalid.sv'},
			{ startIndex: 20, type: 'string.sv'},
			{ startIndex: 21,  type: 'string.escape.invalid.sv'},
			{ startIndex: 23,  type: 'string.escape.sv'},
		]
	}],
	[{
		line: 'bit [8*12:1] stringvar = "Hello world\n";',
		tokens: [
			{ startIndex: 0,  type: 'keyword.bit.sv'},
			{ startIndex: 3, type: ''},
			{ startIndex: 4,  type: 'delimiter.square.sv'},
			{ startIndex: 5, type: 'number.sv'},
			{ startIndex: 6,  type: 'delimiter.sv'},
			{ startIndex: 7, type: 'number.sv'},
			{ startIndex: 9,  type: 'delimiter.sv'},
			{ startIndex: 10, type: 'number.sv'},
			{ startIndex: 11,  type: 'delimiter.square.sv'},
			{ startIndex: 12, type: ''},
			{ startIndex: 13, type: 'identifier.sv'},
			{ startIndex: 22, type: ''},
			{ startIndex: 23,  type: 'delimiter.sv'},
			{ startIndex: 24, type: ''},
			{ startIndex: 25, type: 'string.sv'},
			{ startIndex: 37, type: 'string.escape.sv'},
			{ startIndex: 40, type: 'delimiter.sv'},
		]
	}],
]);
