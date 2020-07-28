/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

'use strict';

import IRichLanguageConfiguration = monaco.languages.LanguageConfiguration;
import ILanguage = monaco.languages.IMonarchLanguage;

export const conf: IRichLanguageConfiguration = {
	comments: {
		lineComment: '//',
		blockComment: ['/*', '*/'],
	},
	brackets: [
		['{', '}'],
		['[', ']'],
		['(', ')']
	],
	autoClosingPairs: [
		{ open: '[', close: ']' },
		{ open: '{', close: '}' },
		{ open: '(', close: ')' },
		{ open: '\'', close: '\'', notIn: ['string', 'comment'] },
		{ open: '"', close: '"', notIn: ['string'] },
	],
	surroundingPairs: [
		{ open: '{', close: '}' },
		{ open: '[', close: ']' },
		{ open: '(', close: ')' },
		{ open: '"', close: '"' },
		{ open: '\'', close: '\'' },
	],
	folding: {
		offSide: false,
		markers: {
			// start: new RegExp("^\\s*(((initial\\s|always(.*)\\s)?begin)|(case(x|z)?)|(class)|(clocking)|(config)|(covergroup)|(function)|(generate)|(interface)|(module)|(package)|(primitive)|(property)|(program)|(sequence)|(specify)|(table)|(task)\\b)"),
			// end: new RegExp("^\\s*((end)|(endcase)|(endclass)|(endclocking)|(endconfig)|(endgroup)|(endfunction)|(endgenerate)|(endinterface)|(endmodule)|(endpackage)|(endprimitive)|(endproperty)|(endprogram)|(endsequence)|(endspecify)|(endtable)|(endtask)\\b)")
			start: new RegExp("^\\s*(((.*\\s)?begin)|(.*\\s)?case(x|z)?|class|clocking|config|covergroup|function|generate|interface|module|package|primitive|property|program|sequence|specify|table|task)\\b"),
			end: new RegExp("^\\s*(end|endcase|endclass|endclocking|endconfig|endgroup|endfunction|endgenerate|endinterface|endmodule|endpackage|endprimitive|endproperty|endprogram|endsequence|endspecify|endtable|endtask)\\b")
		}
	}
};

export const language = <ILanguage>{
	defaultToken: '',
	tokenPostfix: '.sv',

	brackets: [
		{ token: 'delimiter.curly', open: '{', close: '}' },
		{ token: 'delimiter.parenthesis', open: '(', close: ')' },
		{ token: 'delimiter.square', open: '[', close: ']' },
		{ token: 'delimiter.angle', open: '<', close: '>' }
	],

	keywords: [
		'accept_on', 
		'alias', 
		'always', 
		'always_comb', 
		'always_ff', 
		'always_latch',
		'and', 
		'assert', 
		'assign', 
		'assume', 
		'automatic', 
		'before', 
		'begin', 
		'bind',
		'bins', 
		'binsof', 
		'bit',
		'break', 
		'buf', 
		'bufif0', 
		'bufif1', 
		'byte',
		'case', 
		'casex', 
		'casez', 
		'cell', 
		'chandle', 
		'checker', 
		'class', 
		'clocking', 
		'cmos', 
		'config', 
		'const', 
		'constraint', 
		'context', 
		'continue', 
		'cover', 
		'covergroup', 
		'coverpoint', 
		'cross', 
		'deassign', 
		'default', 
		'defparam', 
		'design', 
		'disable', 
		'dist',
		'do', 
		'edge', 
		'else', 
		'end', 
		'endcase', 
		'endchecker', 
		'endclass', 
		'endclocking', 
		'endconfig', 
		'endfunction', 
		'endgenerate', 
		'endgroup', 
		'endinterface', 
		'endmodule', 
		'endpackage',
		'endprimitive', 
		'endprogram', 
		'endproperty', 
		'endspecify', 
		'endsequence', 
		'endtable', 
		'endtask', 
		'enum', 
		'event', 
		'eventually', 
		'expect', 
		'export', 
		'extends', 
		'extern', 
		'final', 
		'first_match',
		'for', 
		'force', 
		'foreach', 
		'forever', 
		'fork', 
		'forkjoin', 
		'function', 
		'generate', 
		'genvar', 
		'global', 
		'highz0', 
		'highz1', 
		'if', 
		'iff', 
		'ifnone',
		'ignore_bins', 
		'illegal_bins', 
		'implements', 
		'implies', 
		'import', 
		'incdir',
		'include', 
		'initial', 
		'inout', 
		'input', 
		'inside', 
		'instance', 
		'int',
		'integer',
		'interconnect',
		'interface', 
		'intersect', 
		'join', 
		'join_any', 
		'join_none', 
		'large', 
		'let',
		'liblist', 
		'library', 
		'local', 
		'localparam', 
		'logic', 
		'longint',
		'macromodule', 
		'matches', 
		'medium', 
		'modport', 
		'module', 
		'nand', 
		'negedge', 
		'nettype', 
		'new', 
		'nexttime', 
		'nmos', 
		'nor', 
		'noshowcancelled', 
		'not', 
		'notif0', 
		'notif1', 
		'null', 
		'or', 
		'output', 
		'package', 
		'packed', 
		'parameter', 
		'pmos', 
		'posedge',
		'primitive', 
		'priority', 
		'program', 
		'property', 
		'protected', 
		'pull0',
		'pull1', 
		'pulldown', 
		'pullup', 
		'pulsestyle_ondetect', 
		'pulsestyle_onevent',
		'pure', 
		'rand', 
		'randc', 
		'randcase', 
		'randsequence', 
		'rcmos', 
		'real',
		'realtime',
		'ref', 
		'reg',
		'reject_on',
		'release', 
		'repeat', 
		'restrict', 
		'return', 
		'rnmos', 
		'rpmos', 
		'rtran', 
		'rtranif0', 
		'rtranif1', 
		's_always', 
		's_eventually', 
		's_nexttime', 
		's_until',
		's_until_with', 
		'scalared', 
		'sequence', 
		'shortint',
		'shortreal',
		'showcancelled', 
		'signed', 
		'small',
		'soft', 
		'solve', 
		'specify', 
		'specparam', 
		'static', 
		'string',
		'strong', 
		'strong0', 
		'strong1', 
		'struct', 
		'super', 
		'supply0', 
		'supply1', 
		'sync_accept_on', 
		'sync_reject_on',
		'table', 
		'tagged', 
		'task', 
		'this', 
		'throughout', 
		'time', 
		'timeprecision',
		'timeunit', 
		'tran', 
		'tranif0', 
		'tranif1', 
		'tri', 
		'tri0', 
		'tri1', 
		'triand',
		'trior', 
		'trireg', 
		'type', 
		'typedef', 
		'union', 
		'unique', 
		'unique0', 
		'unsigned',
		'until', 
		'until_with', 
		'untyped', 
		'use', 
		'uwire', 
		'var', 
		'vectored', 
		'virtual', 
		'void', 
		'wait_order', 
		'wand', 
		'weak', 
		'weak0', 
		'weak1', 
		'while',
		'wildcard', 
		'wire', 
		'with', 
		'within', 
		'wor', 
		'xnor', 
		'xor'
	],

	operators: [
		'=', '>', '<', '!', '~', '?', ':',
		'==', '<=', '>=', '!=', '&&', '||', '++', '--',
		'+', '-', '*', '/', '&', '|', '^', '%', '<<',
		'>>', '>>>', '+=', '-=', '*=', '/=', '&=', '|=',
		'^=', '%=', '<<=', '>>=', '>>>='
	],

	// we include these common regular expressions
	symbols: /[=><!~?:&|+\-*\/\^%]+/,
	escapes: /\\(?:[abfnrtv\\"']|x[0-9A-Fa-f]{1,4}|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})/,
	integersuffix: /(ll|LL|u|U|l|L)?(ll|LL|u|U|l|L)?/,
	floatsuffix: /[fFlL]?/,
	encoding: /u|u8|U|L/,

	// The main tokenizer for our languages
	tokenizer: {
		root: [
			// C++ 11 Raw String
			[/@encoding?R\"(?:([^ ()\\\t]*))\(/, { token: 'string.raw.begin', next: '@raw.$1' }],

			// identifiers and keywords
			[/[a-z_]\w*/, {
				cases: {
					'@keywords': { token: 'keyword.$0' },
					'@default': 'identifier'
				}
			}],

			// whitespace
			{ include: '@whitespace' },

			// [[ attributes ]].
			[/\[\[.*\]\]/, 'annotation'],

			[/^\s*#include/, { token: 'keyword.directive.include', next: '@include' }],

			// Preprocessor directive
			[/^\s*#\s*\w+/, 'keyword'],

			// delimiters and operators
			[/[{}()\[\]]/, '@brackets'],
			[/[<>](?!@symbols)/, '@brackets'],
			[/@symbols/, {
				cases: {
					'@operators': 'delimiter',
					'@default': ''
				}
			}],

			// numbers
			[/\d*\d+[eE]([\-+]?\d+)?(@floatsuffix)/, 'number.float'],
			[/\d*\.\d+([eE][\-+]?\d+)?(@floatsuffix)/, 'number.float'],
			[/0[xX][0-9a-fA-F']*[0-9a-fA-F](@integersuffix)/, 'number.hex'],
			[/0[0-7']*[0-7](@integersuffix)/, 'number.octal'],
			[/0[bB][0-1']*[0-1](@integersuffix)/, 'number.binary'],
			[/\d[\d']*\d(@integersuffix)/, 'number'],
			[/\d(@integersuffix)/, 'number'],

			// delimiter: after number because of .\d floats
			[/[;,.]/, 'delimiter'],

			// strings
			[/"([^"\\]|\\.)*$/, 'string.invalid'],  // non-teminated string
			[/"/, 'string', '@string'],

			// characters
			[/'[^\\']'/, 'string'],
			[/(')(@escapes)(')/, ['string', 'string.escape', 'string']],
			[/'/, 'string.invalid']
		],

		whitespace: [
			[/[ \t\r\n]+/, ''],
			[/\/\*\*(?!\/)/, 'comment.doc', '@doccomment'],
			[/\/\*/, 'comment', '@comment'],
			[/\/\/.*$/, 'comment'],
		],

		comment: [
			[/[^\/*]+/, 'comment'],
			[/\*\//, 'comment', '@pop'],
			[/[\/*]/, 'comment']
		],
		//Identical copy of comment above, except for the addition of .doc
		doccomment: [
			[/[^\/*]+/, 'comment.doc'],
			[/\*\//, 'comment.doc', '@pop'],
			[/[\/*]/, 'comment.doc']
		],

		string: [
			[/[^\\"]+/, 'string'],
			[/@escapes/, 'string.escape'],
			[/\\./, 'string.escape.invalid'],
			[/"/, 'string', '@pop']
		],

		raw: [
			[/(.*)(\))(?:([^ ()\\\t]*))(\")/, {
					cases: {
						'$3==$S2': ['string.raw', 'string.raw.end', 'string.raw.end', { token: 'string.raw.end', next: '@pop' }],
						'@default': ['string.raw', 'string.raw', 'string.raw', 'string.raw']
					}
				}
			],
			[/.*/, 'string.raw']
		],

		include: [
			[/(\s*)(<)([^<>]*)(>)/, ['', 'keyword.directive.include.begin', 'string.include.identifier', { token: 'keyword.directive.include.end', next: '@pop'}]],
			[/(\s*)(")([^"]*)(")/, ['', 'keyword.directive.include.begin', 'string.include.identifier', { token: 'keyword.directive.include.end', next: '@pop'}]]
		]
	},
};
