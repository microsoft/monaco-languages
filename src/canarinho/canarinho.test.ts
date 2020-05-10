/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

'use strict';

import { testTokenization } from '../test/testRunner';

testTokenization('canarinho', [
	// Keywords
	[{
		// line: 'var x = function() { };',
		line: 'variavel x = funcao() { };',
		tokens: [
			{ startIndex: 0, type: 'keyword.cnr' },
			{ startIndex: 8, type: '' },
			{ startIndex: 9, type: 'identifier.cnr' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'delimiter.cnr' },
			{ startIndex: 12, type: '' },
			{ startIndex: 13, type: 'keyword.cnr' },
			{ startIndex: 19, type: 'delimiter.parenthesis.cnr' },
			{ startIndex: 21, type: '' },
			{ startIndex: 22, type: 'delimiter.bracket.cnr' },
			{ startIndex: 23, type: '' },
			{ startIndex: 24, type: 'delimiter.bracket.cnr' },
			{ startIndex: 25, type: 'delimiter.cnr' }
		]
	}],

	[{
		line: '    variavel    ',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 4, type: 'keyword.cnr' },
			{ startIndex: 12, type: '' }
		]
	}],

	// Comments - single line
	[{
		line: '//',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}],

	[{
		line: '    // a comment',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 4, type: 'comment.cnr' }
		]
	}],

	[{
		line: '// a comment',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}],

	[{
		line: '// a comment /*',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}],

	[{
		line: '// a comment /**',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}],

	[{
		line: '//sticky comment',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}],

	[{
		line: 'variavel x = 1; // my comment // is a nice one',
		tokens: [
			{ startIndex: 0, type: 'keyword.cnr' },
			{ startIndex: 8, type: '' },
			{ startIndex: 9, type: 'identifier.cnr' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'delimiter.cnr' },
			{ startIndex: 12, type: '' },
			{ startIndex: 13, type: 'number.cnr' },
			{ startIndex: 14, type: 'delimiter.cnr' },
			{ startIndex: 15, type: '' },
			{ startIndex: 16, type: 'comment.cnr' }
		]
	}],

	// Comments - range comment, single line
	[{
		line: '/* a simple comment */',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}],

	[{
		line: 'variavel x = /* a simple comment */ 1;',
		tokens: [
			{ startIndex: 0, type: 'keyword.cnr' },
			{ startIndex: 8, type: '' },
			{ startIndex: 9, type: 'identifier.cnr' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'delimiter.cnr' },
			{ startIndex: 12, type: '' },
			{ startIndex: 13, type: 'comment.cnr' },
			{ startIndex: 35, type: '' },
			{ startIndex: 36, type: 'number.cnr' },
			{ startIndex: 37, type: 'delimiter.cnr' }
		]
	}],

	[{
		line: 'x = /**/;',
		tokens: [
			{ startIndex: 0, type: 'identifier.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'comment.cnr' },
			{ startIndex: 8, type: 'delimiter.cnr' }
		]
	}],

	[{
		line: 'x = /*/;',
		tokens: [
			{ startIndex: 0, type: 'identifier.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'comment.cnr' }
		]
	}],

	// Comments - range comment, multi lines
	[{
		line: '/* a multiline comment',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}, {
		line: 'can actually span',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}, {
		line: 'multiple lines */',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}],

	[{
		line: 'variavel x = /* start a comment',
		tokens: [
			{ startIndex: 0, type: 'keyword.cnr' },
			{ startIndex: 8, type: '' },
			{ startIndex: 9, type: 'identifier.cnr' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'delimiter.cnr' },
			{ startIndex: 12, type: '' },
			{ startIndex: 13, type: 'comment.cnr' }
		]
	}, {
		line: ' a ',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}, {
		line: 'and end it */ variavel a = 2;',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' },
			{ startIndex: 13, type: '' },
			{ startIndex: 14, type: 'keyword.cnr' },
			{ startIndex: 22, type: '' },
			{ startIndex: 23, type: 'identifier.cnr' },
			{ startIndex: 24, type: '' },
			{ startIndex: 25, type: 'delimiter.cnr' },
			{ startIndex: 26, type: '' },
			{ startIndex: 27, type: 'number.cnr' },
			{ startIndex: 28, type: 'delimiter.cnr' }
		]
	}],

	// Strings
	[{
		line: 'variavel a = \'a\';',
		tokens: [
			{ startIndex: 0, type: 'keyword.cnr' },
			{ startIndex: 8, type: '' },
			{ startIndex: 9, type: 'identifier.cnr' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'delimiter.cnr' },
			{ startIndex: 12, type: '' },
			{ startIndex: 13, type: 'string.cnr' },
			{ startIndex: 16, type: 'delimiter.cnr' }
		]
	}],

	[{
		line: 'b = a + " \'cool\'  "',
		tokens: [
			{ startIndex: 0, type: 'identifier.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'identifier.cnr' },
			{ startIndex: 5, type: '' },
			{ startIndex: 6, type: 'delimiter.cnr' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'string.cnr' }
		]
	}],

	[{
		line: '"escaping \\"quotes\\" is cool"',
		tokens: [
			{ startIndex: 0, type: 'string.cnr' },
			{ startIndex: 10, type: 'string.escape.cnr' },
			{ startIndex: 12, type: 'string.cnr' },
			{ startIndex: 18, type: 'string.escape.cnr' },
			{ startIndex: 20, type: 'string.cnr' },
		]
	}],

	[{
		line: '\'\'\'',
		tokens: [
			{ startIndex: 0, type: 'string.cnr' },
			{ startIndex: 2, type: 'string.invalid.cnr' },
		]
	}],

	[{
		line: '\'\\\'\'',
		tokens: [
			{ startIndex: 0, type: 'string.cnr' },
			{ startIndex: 1, type: 'string.escape.cnr' },
			{ startIndex: 3, type: 'string.cnr' },
		]
	}],

	[{
		line: '\'be careful \\not to escape\'',
		tokens: [
			{ startIndex: 0, type: 'string.cnr' },
			{ startIndex: 12, type: 'string.escape.cnr' },
			{ startIndex: 14, type: 'string.cnr' },
		]
	}],

	// Numbers
	[{
		line: '0',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' }
		]
	}],

	[{
		line: ' 0',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 1, type: 'number.cnr' }
		]
	}],

	[{
		line: ' 0 ',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 1, type: 'number.cnr' },
			{ startIndex: 2, type: '' }
		]
	}],

	[{
		line: '0 ',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 1, type: '' }
		]
	}],

	[{
		line: '0+0',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 1, type: 'delimiter.cnr' },
			{ startIndex: 2, type: 'number.cnr' }
		]
	}],

	[{
		line: '100+10',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 3, type: 'delimiter.cnr' },
			{ startIndex: 4, type: 'number.cnr' }
		]
	}],

	[{
		line: '0 + 0',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'number.cnr' }
		]
	}],

	[{
		line: '0123',
		tokens: [
			{ startIndex: 0, type: 'number.octal.cnr' }
		]
	}],

	[{
		line: '01239',
		tokens: [
			{ startIndex: 0, type: 'number.octal.cnr' },
			{ startIndex: 4, type: 'number.cnr' }
		]
	}],

	[{
		line: '0o123',
		tokens: [
			{ startIndex: 0, type: 'number.octal.cnr' }
		]
	}],

	[{
		line: '0O123',
		tokens: [
			{ startIndex: 0, type: 'number.octal.cnr' }
		]
	}],

	[{
		line: '0x',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 1, type: 'identifier.cnr' }
		]
	}],

	[{
		line: '0x123',
		tokens: [
			{ startIndex: 0, type: 'number.hex.cnr' }
		]
	}],

	[{
		line: '0X123',
		tokens: [
			{ startIndex: 0, type: 'number.hex.cnr' }
		]
	}],

	[{
		line: '0b101',
		tokens: [
			{ startIndex: 0, type: 'number.binary.cnr' }
		]
	}],

	[{
		line: '0B101',
		tokens: [
			{ startIndex: 0, type: 'number.binary.cnr' }
		]
	}],

	// Bigint
	[{
		line: '0n',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' }
		]
	}],

	[{
		line: ' 0n',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 1, type: 'number.cnr' }
		]
	}],

	[{
		line: ' 0n ',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 1, type: 'number.cnr' },
			{ startIndex: 3, type: '' }
		]
	}],

	[{
		line: '0n ',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 2, type: '' }
		]
	}],

	[{
		line: '0n+0n',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: 'number.cnr' }
		]
	}],

	[{
		line: '100n+10n',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 4, type: 'delimiter.cnr' },
			{ startIndex: 5, type: 'number.cnr' }
		]
	}],

	[{
		line: '0n + 0n',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 2, type: '' },
			{ startIndex: 3, type: 'delimiter.cnr' },
			{ startIndex: 4, type: '' },
			{ startIndex: 5, type: 'number.cnr' }
		]
	}],

	[{
		line: '0b101n',
		tokens: [
			{ startIndex: 0, type: 'number.binary.cnr' }
		]
	}],

	[{
		line: '0123n',
		tokens: [
			{ startIndex: 0, type: 'number.octal.cnr' }
		]
	}],

	[{
		line: '0o123n',
		tokens: [
			{ startIndex: 0, type: 'number.octal.cnr' }
		]
	}],

	[{
		line: '0x123n',
		tokens: [
			{ startIndex: 0, type: 'number.hex.cnr' }
		]
	}],

	// Regular Expressions
	[{
		line: '//',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}],

	[{
		line: '/**/',
		tokens: [
			{ startIndex: 0, type: 'comment.cnr' }
		]
	}],

	[{
		line: '/***/',
		tokens: [
			{ startIndex: 0, type: 'comment.doc.cnr' }
		]
	}],

	[{
		line: '5 / 3;',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'number.cnr' },
			{ startIndex: 5, type: 'delimiter.cnr' }
		]
	}],

	// Advanced regular expressions
	[{
		line: '1 / 2; /* comment',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'number.cnr' },
			{ startIndex: 5, type: 'delimiter.cnr' },
			{ startIndex: 6, type: '' },
			{ startIndex: 7, type: 'comment.cnr' }
		]
	}],

	[{
		line: '1 / 2 / x / b;',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'number.cnr' },
			{ startIndex: 5, type: '' },
			{ startIndex: 6, type: 'delimiter.cnr' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'identifier.cnr' },
			{ startIndex: 9, type: '' },
			{ startIndex: 10, type: 'delimiter.cnr' },
			{ startIndex: 11, type: '' },
			{ startIndex: 12, type: 'identifier.cnr' },
			{ startIndex: 13, type: 'delimiter.cnr' }
		]
	}],

	[{
		line: 'x = /foo/.test(\'\')',
		tokens: [
			{ startIndex: 0, type: 'identifier.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'regexp.cnr' },
			{ startIndex: 9, type: 'delimiter.cnr' },
			{ startIndex: 10, type: 'identifier.cnr' },
			{ startIndex: 14, type: 'delimiter.parenthesis.cnr' },
			{ startIndex: 15, type: 'string.cnr' },
			{ startIndex: 17, type: 'delimiter.parenthesis.cnr' }
		]
	}],

	[{
		line: '/foo/',
		tokens: [
			{ startIndex: 0, type: 'regexp.cnr' }
		]
	}],

	[{
		line: '/foo/g',
		tokens: [
			{ startIndex: 0, type: 'regexp.cnr' },
			{ startIndex: 5, type: 'keyword.other.cnr' }
		]
	}],

	[{
		line: '/foo/gimsuy',
		tokens: [
			{ startIndex: 0, type: 'regexp.cnr' },
			{ startIndex: 5, type: 'keyword.other.cnr' }
		]
	}],

	[{
		line: '/foo/q', // invalid flag
		tokens: [
			{ startIndex: 0, type: 'delimiter.cnr' },
			{ startIndex: 1, type: 'identifier.cnr' },
			{ startIndex: 4, type: 'delimiter.cnr' },
			{ startIndex: 5, type: 'identifier.cnr' }
		]
	}],

	[{
		line: 'x = 1 + f(2 / 3, /foo/)',
		tokens: [
			{ startIndex: 0, type: 'identifier.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'number.cnr' },
			{ startIndex: 5, type: '' },
			{ startIndex: 6, type: 'delimiter.cnr' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'identifier.cnr' },
			{ startIndex: 9, type: 'delimiter.parenthesis.cnr' },
			{ startIndex: 10, type: 'number.cnr' },
			{ startIndex: 11, type: '' },
			{ startIndex: 12, type: 'delimiter.cnr' },
			{ startIndex: 13, type: '' },
			{ startIndex: 14, type: 'number.cnr' },
			{ startIndex: 15, type: 'delimiter.cnr' },
			{ startIndex: 16, type: '' },
			{ startIndex: 17, type: 'regexp.cnr' },
			{ startIndex: 22, type: 'delimiter.parenthesis.cnr' }
		]
	}],

	[{
		line: 'a /ads/ b;',
		tokens: [
			{ startIndex: 0, type: 'identifier.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: 'identifier.cnr' },
			{ startIndex: 6, type: 'delimiter.cnr' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'identifier.cnr' },
			{ startIndex: 9, type: 'delimiter.cnr' }
		]
	}],

	[{
		line: '1/(2/3)/2/3;',
		tokens: [
			{ startIndex: 0, type: 'number.cnr' },
			{ startIndex: 1, type: 'delimiter.cnr' },
			{ startIndex: 2, type: 'delimiter.parenthesis.cnr' },
			{ startIndex: 3, type: 'number.cnr' },
			{ startIndex: 4, type: 'delimiter.cnr' },
			{ startIndex: 5, type: 'number.cnr' },
			{ startIndex: 6, type: 'delimiter.parenthesis.cnr' },
			{ startIndex: 7, type: 'delimiter.cnr' },
			{ startIndex: 8, type: 'number.cnr' },
			{ startIndex: 9, type: 'delimiter.cnr' },
			{ startIndex: 10, type: 'number.cnr' },
			{ startIndex: 11, type: 'delimiter.cnr' }
		]
	}],

	[{
		line: '{ key: 123 }',
		tokens: [
			{ startIndex: 0, type: 'delimiter.bracket.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'identifier.cnr' },
			{ startIndex: 5, type: 'delimiter.cnr' },
			{ startIndex: 6, type: '' },
			{ startIndex: 7, type: 'number.cnr' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'delimiter.bracket.cnr' }
		]
	}],

	[{
		line: '[1,2,3]',
		tokens: [
			{ startIndex: 0, type: 'delimiter.square.cnr' },
			{ startIndex: 1, type: 'number.cnr' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: 'number.cnr' },
			{ startIndex: 4, type: 'delimiter.cnr' },
			{ startIndex: 5, type: 'number.cnr' },
			{ startIndex: 6, type: 'delimiter.square.cnr' }
		]
	}],

	[{
		line: 'foo(123);',
		tokens: [
			{ startIndex: 0, type: 'identifier.cnr' },
			{ startIndex: 3, type: 'delimiter.parenthesis.cnr' },
			{ startIndex: 4, type: 'number.cnr' },
			{ startIndex: 7, type: 'delimiter.parenthesis.cnr' },
			{ startIndex: 8, type: 'delimiter.cnr' }
		]
	}],

	[{
		line: '{a:{b:[]}}',
		tokens: [
			{ startIndex: 0, type: 'delimiter.bracket.cnr' },
			{ startIndex: 1, type: 'identifier.cnr' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: 'delimiter.bracket.cnr' },
			{ startIndex: 4, type: 'identifier.cnr' },
			{ startIndex: 5, type: 'delimiter.cnr' },
			{ startIndex: 6, type: 'delimiter.square.cnr' },
			{ startIndex: 8, type: 'delimiter.bracket.cnr' }
		]
	}],

	[{
		line: 'x = "[{()}]"',
		tokens: [
			{ startIndex: 0, type: 'identifier.cnr' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.cnr' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'string.cnr' }
		]
	}],


	[{
		line: 'test ? 1 : 2',
		tokens: [
			{ startIndex: 0, type: 'identifier.cnr' },
			{ startIndex: 4, type: '' },
			{ startIndex: 5, type: 'delimiter.cnr' },
			{ startIndex: 6, type: '' },
			{ startIndex: 7, type: 'number.cnr' },
			{ startIndex: 8, type: '' },
			{ startIndex: 9, type: 'delimiter.cnr' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'number.cnr' },
		]
	}],

	[{
		line: 'couldBeNullish ?? 1',
		tokens: [
			{ startIndex: 0, type: 'identifier.cnr' },
			{ startIndex: 14, type: '' },
			{ startIndex: 15, type: 'delimiter.cnr' },
			{ startIndex: 17, type: '' },
			{ startIndex: 18, type: 'number.cnr' }
		]
	}],


	[{
		line: '`${5 + \'x\' + 3}a${4}`',
		tokens: [
			{ startIndex: 0, type: 'string.cnr' },
			{ startIndex: 1, type: 'delimiter.bracket.cnr' },
			{ startIndex: 3, type: 'number.cnr' },
			{ startIndex: 4, type: '' },
			{ startIndex: 5, type: 'delimiter.cnr' },
			{ startIndex: 6, type: '' },
			{ startIndex: 7, type: 'string.cnr' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'delimiter.cnr' },
			{ startIndex: 12, type: '' },
			{ startIndex: 13, type: 'number.cnr' },
			{ startIndex: 14, type: 'delimiter.bracket.cnr' },
			{ startIndex: 15, type: 'string.cnr' },
			{ startIndex: 16, type: 'delimiter.bracket.cnr' },
			{ startIndex: 18, type: 'number.cnr' },
			{ startIndex: 19, type: 'delimiter.bracket.cnr' },
			{ startIndex: 20, type: 'string.cnr' },

		]
	}]

]);
