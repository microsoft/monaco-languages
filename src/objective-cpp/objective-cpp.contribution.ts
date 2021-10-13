import { registerLanguage } from '../_.contribution';

registerLanguage({
	id: 'objective-cpp',
	extensions: ['.mm'],
	aliases: ['Objective-Cpp', 'Objective-C++'],
	loader: () => import('./objective-cpp')
});
