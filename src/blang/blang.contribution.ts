import { registerLanguage } from '../_.contribution';

registerLanguage({
	id: 'blang',
	extensions: ['.blang'],
	aliases: ['blang', 'Blang', 'Brahma Language'],
	loader: () => import('./blang')
});
