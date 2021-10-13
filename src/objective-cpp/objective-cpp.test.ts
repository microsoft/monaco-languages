/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

import { testTokenization } from '../test/testRunner';

testTokenization('objective-cpp', [
	// Keywords
	[
		{
			line: '-(id) initWithParams:(id<anObject>) aHandler withDeviceStateManager:(id<anotherObject>) deviceStateManager',
			tokens: [
				{ startIndex: 0, type: '' },
				{ startIndex: 1, type: 'delimiter.parenthesis.objective-cpp' },
				{ startIndex: 2, type: 'keyword.objective-cpp' },
				{ startIndex: 4, type: 'delimiter.parenthesis.objective-cpp' },
				{ startIndex: 5, type: 'white.objective-cpp' },
				{ startIndex: 6, type: 'identifier.objective-cpp' },
				{ startIndex: 20, type: 'delimiter.objective-cpp' },
				{ startIndex: 21, type: 'delimiter.parenthesis.objective-cpp' },
				{ startIndex: 22, type: 'keyword.objective-cpp' },
				{ startIndex: 24, type: 'delimiter.angle.objective-cpp' },
				{ startIndex: 25, type: 'identifier.objective-cpp' },
				{ startIndex: 33, type: 'delimiter.angle.objective-cpp' },
				{ startIndex: 34, type: 'delimiter.parenthesis.objective-cpp' },
				{ startIndex: 35, type: 'white.objective-cpp' },
				{ startIndex: 36, type: 'identifier.objective-cpp' },
				{ startIndex: 44, type: 'white.objective-cpp' },
				{ startIndex: 45, type: 'identifier.objective-cpp' },
				{ startIndex: 67, type: 'delimiter.objective-cpp' },
				{ startIndex: 68, type: 'delimiter.parenthesis.objective-cpp' },
				{ startIndex: 69, type: 'keyword.objective-cpp' },
				{ startIndex: 71, type: 'delimiter.angle.objective-cpp' },
				{ startIndex: 72, type: 'identifier.objective-cpp' },
				{ startIndex: 85, type: 'delimiter.angle.objective-cpp' },
				{ startIndex: 86, type: 'delimiter.parenthesis.objective-cpp' },
				{ startIndex: 87, type: 'white.objective-cpp' },
				{ startIndex: 88, type: 'identifier.objective-cpp' }
			]
		}
	],

	// Comments - single line
	[
		{
			line: '//',
			tokens: [{ startIndex: 0, type: 'comment.objective-cpp' }]
		}
	],

	[
		{
			line: '    // a comment',
			tokens: [
				{ startIndex: 0, type: 'white.objective-cpp' },
				{ startIndex: 4, type: 'comment.objective-cpp' }
			]
		}
	],

	[
		{
			line: '// a comment',
			tokens: [{ startIndex: 0, type: 'comment.objective-cpp' }]
		}
	],

	[
		{
			line: '//sticky comment',
			tokens: [{ startIndex: 0, type: 'comment.objective-cpp' }]
		}
	],

	[
		{
			line: '/almost a comment',
			tokens: [
				{ startIndex: 0, type: 'operator.objective-cpp' },
				{ startIndex: 1, type: 'identifier.objective-cpp' },
				{ startIndex: 7, type: 'white.objective-cpp' },
				{ startIndex: 8, type: 'identifier.objective-cpp' },
				{ startIndex: 9, type: 'white.objective-cpp' },
				{ startIndex: 10, type: 'identifier.objective-cpp' }
			]
		}
	],

	[
		{
			line: '1 / 2; /* comment',
			tokens: [
				{ startIndex: 0, type: 'number.objective-cpp' },
				{ startIndex: 1, type: 'white.objective-cpp' },
				{ startIndex: 2, type: 'operator.objective-cpp' },
				{ startIndex: 3, type: 'white.objective-cpp' },
				{ startIndex: 4, type: 'number.objective-cpp' },
				{ startIndex: 5, type: 'delimiter.objective-cpp' },
				{ startIndex: 6, type: 'white.objective-cpp' },
				{ startIndex: 7, type: 'comment.objective-cpp' }
			]
		}
	],

	[
		{
			line: 'int x = 1; // my comment // is a nice one',
			tokens: [
				{ startIndex: 0, type: 'keyword.objective-cpp' },
				{ startIndex: 3, type: 'white.objective-cpp' },
				{ startIndex: 4, type: 'identifier.objective-cpp' },
				{ startIndex: 5, type: 'white.objective-cpp' },
				{ startIndex: 6, type: 'operator.objective-cpp' },
				{ startIndex: 7, type: 'white.objective-cpp' },
				{ startIndex: 8, type: 'number.objective-cpp' },
				{ startIndex: 9, type: 'delimiter.objective-cpp' },
				{ startIndex: 10, type: 'white.objective-cpp' },
				{ startIndex: 11, type: 'comment.objective-cpp' }
			]
		}
	],

	// Comments - range comment, single line
	[
		{
			line: '/* a simple comment */',
			tokens: [{ startIndex: 0, type: 'comment.objective-cpp' }]
		}
	],

	[
		{
			line: 'int x = /* embedded comment */ 1;',
			tokens: [
				{ startIndex: 0, type: 'keyword.objective-cpp' },
				{ startIndex: 3, type: 'white.objective-cpp' },
				{ startIndex: 4, type: 'identifier.objective-cpp' },
				{ startIndex: 5, type: 'white.objective-cpp' },
				{ startIndex: 6, type: 'operator.objective-cpp' },
				{ startIndex: 7, type: 'white.objective-cpp' },
				{ startIndex: 8, type: 'comment.objective-cpp' },
				{ startIndex: 30, type: 'white.objective-cpp' },
				{ startIndex: 31, type: 'number.objective-cpp' },
				{ startIndex: 32, type: 'delimiter.objective-cpp' }
			]
		}
	],

	[
		{
			line: 'int x = /* comment and syntax error*/ 1; */',
			tokens: [
				{ startIndex: 0, type: 'keyword.objective-cpp' },
				{ startIndex: 3, type: 'white.objective-cpp' },
				{ startIndex: 4, type: 'identifier.objective-cpp' },
				{ startIndex: 5, type: 'white.objective-cpp' },
				{ startIndex: 6, type: 'operator.objective-cpp' },
				{ startIndex: 7, type: 'white.objective-cpp' },
				{ startIndex: 8, type: 'comment.objective-cpp' },
				{ startIndex: 37, type: 'white.objective-cpp' },
				{ startIndex: 38, type: 'number.objective-cpp' },
				{ startIndex: 39, type: 'delimiter.objective-cpp' },
				{ startIndex: 40, type: 'white.objective-cpp' },
				{ startIndex: 41, type: 'operator.objective-cpp' }
			]
		}
	],

	[
		{
			line: 'x = /**/;',
			tokens: [
				{ startIndex: 0, type: 'identifier.objective-cpp' },
				{ startIndex: 1, type: 'white.objective-cpp' },
				{ startIndex: 2, type: 'operator.objective-cpp' },
				{ startIndex: 3, type: 'white.objective-cpp' },
				{ startIndex: 4, type: 'comment.objective-cpp' },
				{ startIndex: 8, type: 'delimiter.objective-cpp' }
			]
		}
	],

	[
		{
			line: 'x = /*/;',
			tokens: [
				{ startIndex: 0, type: 'identifier.objective-cpp' },
				{ startIndex: 1, type: 'white.objective-cpp' },
				{ startIndex: 2, type: 'operator.objective-cpp' },
				{ startIndex: 3, type: 'white.objective-cpp' },
				{ startIndex: 4, type: 'comment.objective-cpp' }
			]
		}
	],

	// Non-Alpha Keywords
	[
		{
			line: '#import <GTLT.h>',
			tokens: [
				{ startIndex: 0, type: 'keyword.objective-cpp' },
				{ startIndex: 7, type: 'white.objective-cpp' },
				{ startIndex: 8, type: 'delimiter.angle.objective-cpp' },
				{ startIndex: 9, type: 'identifier.objective-cpp' },
				{ startIndex: 13, type: '' },
				{ startIndex: 14, type: 'identifier.objective-cpp' },
				{ startIndex: 15, type: 'delimiter.angle.objective-cpp' }
			]
		}
	],

	// Numbers
	[
		{
			line: '0 ',
			tokens: [
				{ startIndex: 0, type: 'number.objective-cpp' },
				{ startIndex: 1, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '0x ',
			tokens: [
				{ startIndex: 0, type: 'number.hex.objective-cpp' },
				{ startIndex: 2, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '0x123 ',
			tokens: [
				{ startIndex: 0, type: 'number.hex.objective-cpp' },
				{ startIndex: 5, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '23.5 ',
			tokens: [
				{ startIndex: 0, type: 'number.float.objective-cpp' },
				{ startIndex: 4, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '23.5e3 ',
			tokens: [
				{ startIndex: 0, type: 'number.float.objective-cpp' },
				{ startIndex: 6, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '23.5E3 ',
			tokens: [
				{ startIndex: 0, type: 'number.float.objective-cpp' },
				{ startIndex: 6, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '23.5F ',
			tokens: [
				{ startIndex: 0, type: 'number.float.objective-cpp' },
				{ startIndex: 5, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '23.5f ',
			tokens: [
				{ startIndex: 0, type: 'number.float.objective-cpp' },
				{ startIndex: 5, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '1.72E3F ',
			tokens: [
				{ startIndex: 0, type: 'number.float.objective-cpp' },
				{ startIndex: 7, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '1.72E3f ',
			tokens: [
				{ startIndex: 0, type: 'number.float.objective-cpp' },
				{ startIndex: 7, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '1.72e3F ',
			tokens: [
				{ startIndex: 0, type: 'number.float.objective-cpp' },
				{ startIndex: 7, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '1.72e3f ',
			tokens: [
				{ startIndex: 0, type: 'number.float.objective-cpp' },
				{ startIndex: 7, type: 'white.objective-cpp' }
			]
		}
	],

	[
		{
			line: '0+0',
			tokens: [
				{ startIndex: 0, type: 'number.objective-cpp' },
				{ startIndex: 1, type: 'operator.objective-cpp' },
				{ startIndex: 2, type: 'number.objective-cpp' }
			]
		}
	],

	[
		{
			line: '100+10',
			tokens: [
				{ startIndex: 0, type: 'number.objective-cpp' },
				{ startIndex: 3, type: 'operator.objective-cpp' },
				{ startIndex: 4, type: 'number.objective-cpp' }
			]
		}
	],

	[
		{
			line: '0 + 0',
			tokens: [
				{ startIndex: 0, type: 'number.objective-cpp' },
				{ startIndex: 1, type: 'white.objective-cpp' },
				{ startIndex: 2, type: 'operator.objective-cpp' },
				{ startIndex: 3, type: 'white.objective-cpp' },
				{ startIndex: 4, type: 'number.objective-cpp' }
			]
		}
	]
]);
