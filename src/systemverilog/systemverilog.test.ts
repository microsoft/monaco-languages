/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

'use strict';

import { testTokenization } from '../test/testRunner';

testTokenization('sv', [
	// Keywords
	[{
		line: 'int _tmain(int argc, _TCHAR* argv[])',
		tokens: [
			{ startIndex: 0, type: 'keyword.int.sv' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'identifier.sv' },
			{ startIndex: 10, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 11, type: 'keyword.int.sv' },
			{ startIndex: 14, type: '' },
			{ startIndex: 15, type: 'identifier.sv' },
			{ startIndex: 19, type: 'delimiter.sv' },
			{ startIndex: 20, type: '' },
			{ startIndex: 21, type: 'identifier.sv' },
			{ startIndex: 27, type: 'delimiter.sv' },
			{ startIndex: 28, type: '' },
			{ startIndex: 29, type: 'identifier.sv' },
			{ startIndex: 33, type: 'delimiter.square.sv' },
			{ startIndex: 35, type: 'delimiter.parenthesis.sv' }
		]
	}],

	// Comments - single line
	[{
		line: '//',
		tokens: [
			{ startIndex: 0, type: 'comment.sv' }
		]
	}],

	[{
		line: '    // a comment',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 4, type: 'comment.sv' }
		]
	}],

	[{
		line: '// a comment',
		tokens: [
			{ startIndex: 0, type: 'comment.sv' }
		]
	}],

	[{
		line: '//sticky comment',
		tokens: [
			{ startIndex: 0, type: 'comment.sv' }
		]
	}],

	[{
		line: '/almost a comment',
		tokens: [
			{ startIndex: 0, type: 'delimiter.sv' },
			{ startIndex: 1, type: 'identifier.sv' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'identifier.sv' },
			{ startIndex: 9, type: '' },
			{ startIndex: 10, type: 'identifier.sv' }
		]
	}],

	[{
		line: '/* //*/ a',
		tokens: [
			{ startIndex: 0, type: 'comment.sv' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'identifier.sv' }
		]
	}],

	[{
		line: '1 / 2; /* comment',
		tokens: [
			{ startIndex: 0, type: 'number.sv' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.sv' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'number.sv' },
			{ startIndex: 5, type: 'delimiter.sv' },
			{ startIndex: 6, type: '' },
			{ startIndex: 7, type: 'comment.sv' }
		]
	}],

	[{
		line: 'int x = 1; // my comment // is a nice one',
		tokens: [
			{ startIndex: 0, type: 'keyword.int.sv' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'identifier.sv' },
			{ startIndex: 5, type: '' },
			{ startIndex: 6, type: 'delimiter.sv' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'number.sv' },
			{ startIndex: 9, type: 'delimiter.sv' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'comment.sv' }
		]
	}],

	// Comments - range comment, single line
	[{
		line: '/* a simple comment */',
		tokens: [
			{ startIndex: 0, type: 'comment.sv' }
		]
	}],

	[{
		line: 'int x = /* a simple comment */ 1;',
		tokens: [
			{ startIndex: 0, type: 'keyword.int.sv' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'identifier.sv' },
			{ startIndex: 5, type: '' },
			{ startIndex: 6, type: 'delimiter.sv' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'comment.sv' },
			{ startIndex: 30, type: '' },
			{ startIndex: 31, type: 'number.sv' },
			{ startIndex: 32, type: 'delimiter.sv' }
		]
	}],

	[{
		line: 'int x = /* comment */ 1; */',
		tokens: [
			{ startIndex: 0, type: 'keyword.int.sv' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'identifier.sv' },
			{ startIndex: 5, type: '' },
			{ startIndex: 6, type: 'delimiter.sv' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'comment.sv' },
			{ startIndex: 21, type: '' },
			{ startIndex: 22, type: 'number.sv' },
			{ startIndex: 23, type: 'delimiter.sv' },
			{ startIndex: 24, type: '' }
		]
	}],

	[{
		line: 'x = /**/;',
		tokens: [
			{ startIndex: 0, type: 'identifier.sv' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.sv' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'comment.sv' },
			{ startIndex: 8, type: 'delimiter.sv' }
		]
	}],

	[{
		line: 'x = /*/;',
		tokens: [
			{ startIndex: 0, type: 'identifier.sv' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.sv' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'comment.sv' }
		]
	}],

	// Numbers
	[{
		line: '0',
		tokens: [
			{ startIndex: 0, type: 'number.sv' }
		]
	}],

	[{
		line: '12l',
		tokens: [
			{ startIndex: 0, type: 'number.sv' }
		]
	}],

	[{
		line: '34U',
		tokens: [
			{ startIndex: 0, type: 'number.sv' }
		]
	}],

	[{
		line: '55LL',
		tokens: [
			{ startIndex: 0, type: 'number.sv' }
		]
	}],

	[{
		line: '34ul',
		tokens: [
			{ startIndex: 0, type: 'number.sv' }
		]
	}],

	[{
		line: '55llU',
		tokens: [
			{ startIndex: 0, type: 'number.sv' }
		]
	}],

	[{
		line: '5\'5llU',
		tokens: [
			{ startIndex: 0, type: 'number.sv' }
		]
	}],

	[{
		line: '100\'000\'000',
		tokens: [
			{ startIndex: 0, type: 'number.sv' }
		]
	}],

	[{
		line: '0x100\'aafllU',
		tokens: [
			{ startIndex: 0, type: 'number.hex.sv' }
		]
	}],

	[{
		line: '0342\'325',
		tokens: [
			{ startIndex: 0, type: 'number.octal.sv' }
		]
	}],

	[{
		line: '0x123',
		tokens: [
			{ startIndex: 0, type: 'number.hex.sv' }
		]
	}],

	[{
		line: '23.5',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '23.5e3',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '23.5E3',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '23.5F',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '23.5f',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '1.72E3F',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '1.72E3f',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '1.72e3F',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '1.72e3f',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '23.5L',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '23.5l',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '1.72E3L',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '1.72E3l',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '1.72e3L',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '1.72e3l',
		tokens: [
			{ startIndex: 0, type: 'number.float.sv' }
		]
	}],

	[{
		line: '0+0',
		tokens: [
			{ startIndex: 0, type: 'number.sv' },
			{ startIndex: 1, type: 'delimiter.sv' },
			{ startIndex: 2, type: 'number.sv' }
		]
	}],

	[{
		line: '100+10',
		tokens: [
			{ startIndex: 0, type: 'number.sv' },
			{ startIndex: 3, type: 'delimiter.sv' },
			{ startIndex: 4, type: 'number.sv' }
		]
	}],

	[{
		line: '0 + 0',
		tokens: [
			{ startIndex: 0, type: 'number.sv' },
			{ startIndex: 1, type: '' },
			{ startIndex: 2, type: 'delimiter.sv' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'number.sv' }
		]
	}],

	// Monarch Generated
	[{
		line: '#include<iostream>',
		tokens: [
			{ startIndex: 0, type: 'keyword.directive.include.sv' },
			{ startIndex: 8, type: 'keyword.directive.include.begin.sv' },
			{ startIndex: 9, type: 'string.include.identifier.sv' },
			{ startIndex: 17, type: 'keyword.directive.include.end.sv' }
		]
	}, {
		line: '#include "/path/to/my/file.h"',
		tokens: [
			{ startIndex: 0, type: 'keyword.directive.include.sv' },
			{ startIndex: 8, type: '' },
			{ startIndex: 9, type: 'keyword.directive.include.begin.sv' },
			{ startIndex: 10, type: 'string.include.identifier.sv' },
			{ startIndex: 28, type: 'keyword.directive.include.end.sv' }
		]
	}, {
		line: '',
		tokens: [

		]
	}, {
		line: '#ifdef VAR',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv' },
			{ startIndex: 6, type: '' },
			{ startIndex: 7, type: 'identifier.sv' }
		]
	}, {
		line: '#define SUM(A,B) (A) + (B)',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'identifier.sv' },
			{ startIndex: 11, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 12, type: 'identifier.sv' },
			{ startIndex: 13, type: 'delimiter.sv' },
			{ startIndex: 14, type: 'identifier.sv' },
			{ startIndex: 15, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 16, type: '' },
			{ startIndex: 17, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 18, type: 'identifier.sv' },
			{ startIndex: 19, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 20, type: '' },
			{ startIndex: 21, type: 'delimiter.sv' },
			{ startIndex: 22, type: '' },
			{ startIndex: 23, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 24, type: 'identifier.sv' },
			{ startIndex: 25, type: 'delimiter.parenthesis.sv' }
		]
	}, {
		line: '',
		tokens: [

		]
	}, {
		line: 'int main(int argc, char** argv)',
		tokens: [
			{ startIndex: 0, type: 'keyword.int.sv' },
			{ startIndex: 3, type: '' },
			{ startIndex: 4, type: 'identifier.sv' },
			{ startIndex: 8, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 9, type: 'keyword.int.sv' },
			{ startIndex: 12, type: '' },
			{ startIndex: 13, type: 'identifier.sv' },
			{ startIndex: 17, type: 'delimiter.sv' },
			{ startIndex: 18, type: '' },
			{ startIndex: 19, type: 'keyword.char.sv' },
			{ startIndex: 23, type: '' },
			{ startIndex: 26, type: 'identifier.sv' },
			{ startIndex: 30, type: 'delimiter.parenthesis.sv' }
		]
	}, {
		line: '{',
		tokens: [
			{ startIndex: 0, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '	return 0;',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 1, type: 'keyword.return.sv' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'number.sv' },
			{ startIndex: 9, type: 'delimiter.sv' }
		]
	}, {
		line: '}',
		tokens: [
			{ startIndex: 0, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '',
		tokens: [

		]
	}, {
		line: 'namespace TestSpace',
		tokens: [
			{ startIndex: 0, type: 'keyword.namespace.sv' },
			{ startIndex: 9, type: '' },
			{ startIndex: 10, type: 'identifier.sv' }
		]
	}, {
		line: '{',
		tokens: [
			{ startIndex: 0, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '	using Asdf.CDE;',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 1, type: 'keyword.using.sv' },
			{ startIndex: 6, type: '' },
			{ startIndex: 7, type: 'identifier.sv' },
			{ startIndex: 11, type: 'delimiter.sv' },
			{ startIndex: 12, type: 'identifier.sv' },
			{ startIndex: 15, type: 'delimiter.sv' }
		]
	}, {
		line: '	template <typename T>',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 1, type: 'keyword.template.sv' },
			{ startIndex: 9, type: '' },
			{ startIndex: 10, type: 'delimiter.angle.sv' },
			{ startIndex: 11, type: 'keyword.typename.sv' },
			{ startIndex: 19, type: '' },
			{ startIndex: 20, type: 'identifier.sv' },
			{ startIndex: 21, type: 'delimiter.angle.sv' }
		]
	}, {
		line: '	class CoolClass : protected BaseClass',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 1, type: 'keyword.class.sv' },
			{ startIndex: 6, type: '' },
			{ startIndex: 7, type: 'identifier.sv' },
			{ startIndex: 16, type: '' },
			{ startIndex: 17, type: 'delimiter.sv' },
			{ startIndex: 18, type: '' },
			{ startIndex: 19, type: 'keyword.protected.sv' },
			{ startIndex: 28, type: '' },
			{ startIndex: 29, type: 'identifier.sv' }
		]
	}, {
		line: '	{',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 1, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '		private:',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 2, type: 'keyword.private.sv' },
			{ startIndex: 9, type: 'delimiter.sv' }
		]
	}, {
		line: '		',
		tokens: [
			{ startIndex: 0, type: '' }
		]
	}, {
		line: '		static T field;',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 2, type: 'keyword.static.sv' },
			{ startIndex: 8, type: '' },
			{ startIndex: 9, type: 'identifier.sv' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'identifier.sv' },
			{ startIndex: 16, type: 'delimiter.sv' }
		]
	}, {
		line: '		',
		tokens: [
			{ startIndex: 0, type: '' }
		]
	}, {
		line: '		public:',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 2, type: 'keyword.public.sv' },
			{ startIndex: 8, type: 'delimiter.sv' }
		]
	}, {
		line: '		',
		tokens: [
			{ startIndex: 0, type: '' }
		]
	}, {
		line: '		[[deprecated]]',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 2, type: 'annotation.sv' }
		]
	}, {
		line: '		foo method() const override',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 2, type: 'identifier.sv' },
			{ startIndex: 5, type: '' },
			{ startIndex: 6, type: 'identifier.sv' },
			{ startIndex: 12, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 14, type: '' },
			{ startIndex: 15, type: 'keyword.const.sv' },
			{ startIndex: 20, type: '' },
			{ startIndex: 21, type: 'keyword.override.sv' }
		]
	}, {
		line: '		{',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 2, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '			auto s = new Bar();',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 3, type: 'keyword.auto.sv' },
			{ startIndex: 7, type: '' },
			{ startIndex: 8, type: 'identifier.sv' },
			{ startIndex: 9, type: '' },
			{ startIndex: 10, type: 'delimiter.sv' },
			{ startIndex: 11, type: '' },
			{ startIndex: 12, type: 'keyword.new.sv' },
			{ startIndex: 15, type: '' },
			{ startIndex: 16, type: 'identifier.sv' },
			{ startIndex: 19, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 21, type: 'delimiter.sv' }
		]
	}, {
		line: '			',
		tokens: [
			{ startIndex: 0, type: '' }
		]
	}, {
		line: '			if (s.field) {',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 3, type: 'keyword.if.sv' },
			{ startIndex: 5, type: '' },
			{ startIndex: 6, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 7, type: 'identifier.sv' },
			{ startIndex: 8, type: 'delimiter.sv' },
			{ startIndex: 9, type: 'identifier.sv' },
			{ startIndex: 14, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 15, type: '' },
			{ startIndex: 16, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '				for(const auto & b : s.field) {',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 4, type: 'keyword.for.sv' },
			{ startIndex: 7, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 8, type: 'keyword.const.sv' },
			{ startIndex: 13, type: '' },
			{ startIndex: 14, type: 'keyword.auto.sv' },
			{ startIndex: 18, type: '' },
			{ startIndex: 19, type: 'delimiter.sv' },
			{ startIndex: 20, type: '' },
			{ startIndex: 21, type: 'identifier.sv' },
			{ startIndex: 22, type: '' },
			{ startIndex: 23, type: 'delimiter.sv' },
			{ startIndex: 24, type: '' },
			{ startIndex: 25, type: 'identifier.sv' },
			{ startIndex: 26, type: 'delimiter.sv' },
			{ startIndex: 27, type: 'identifier.sv' },
			{ startIndex: 32, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 33, type: '' },
			{ startIndex: 34, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '					break;',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 5, type: 'keyword.break.sv' },
			{ startIndex: 10, type: 'delimiter.sv' }
		]
	}, {
		line: '				}',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 4, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '			}',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 3, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '		}',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 2, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '		',
		tokens: [
			{ startIndex: 0, type: '' }
		]
	}, {
		line: '		std::string s = "hello wordld\\n";',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 2, type: 'identifier.sv' },
			{ startIndex: 5, type: '' },
			{ startIndex: 7, type: 'identifier.sv' },
			{ startIndex: 13, type: '' },
			{ startIndex: 14, type: 'identifier.sv' },
			{ startIndex: 15, type: '' },
			{ startIndex: 16, type: 'delimiter.sv' },
			{ startIndex: 17, type: '' },
			{ startIndex: 18, type: 'string.sv' },
			{ startIndex: 31, type: 'string.escape.sv' },
			{ startIndex: 33, type: 'string.sv' },
			{ startIndex: 34, type: 'delimiter.sv' }
		]
	}, {
		line: '		',
		tokens: [
			{ startIndex: 0, type: '' }
		]
	}, {
		line: '		int number = 123\'123\'123Ull;',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 2, type: 'keyword.int.sv' },
			{ startIndex: 5, type: '' },
			{ startIndex: 6, type: 'identifier.sv' },
			{ startIndex: 12, type: '' },
			{ startIndex: 13, type: 'delimiter.sv' },
			{ startIndex: 14, type: '' },
			{ startIndex: 15, type: 'number.sv' },
			{ startIndex: 29, type: 'delimiter.sv' }
		]
	}, {
		line: '	}',
		tokens: [
			{ startIndex: 0, type: '' },
			{ startIndex: 1, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '}',
		tokens: [
			{ startIndex: 0, type: 'delimiter.curly.sv' }
		]
	}, {
		line: '',
		tokens: [

		]
	}, {
		line: '#endif',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv' }
		]
	}, {
		line: '#    ifdef VAR',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv' },
			{ startIndex: 10, type: '' },
			{ startIndex: 11, type: 'identifier.sv' }
		]
	}, {
		line: '#	define SUM(A,B) (A) + (B)',
		tokens: [
			{ startIndex: 0, type: 'keyword.sv' },
			{ startIndex: 8, type: '' },
			{ startIndex: 9, type: 'identifier.sv' },
			{ startIndex: 12, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 13, type: 'identifier.sv' },
			{ startIndex: 14, type: 'delimiter.sv' },
			{ startIndex: 15, type: 'identifier.sv' },
			{ startIndex: 16, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 17, type: '' },
			{ startIndex: 18, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 19, type: 'identifier.sv' },
			{ startIndex: 20, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 21, type: '' },
			{ startIndex: 22, type: 'delimiter.sv' },
			{ startIndex: 23, type: '' },
			{ startIndex: 24, type: 'delimiter.parenthesis.sv' },
			{ startIndex: 25, type: 'identifier.sv' },
			{ startIndex: 26, type: 'delimiter.parenthesis.sv' }
		]
	}, {
		line: 'uR"V0G0N(abc)V0G0N"def',
		tokens: [
			{ startIndex: 0, type: 'string.raw.begin.sv' },
			{ startIndex: 9, type: 'string.raw.sv' },
			{ startIndex: 12, type: 'string.raw.end.sv' },
			{ startIndex: 19, type: 'identifier.sv' }
		]
	}]
]);
